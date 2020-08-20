/*
 * An interactive interpreter for Datalog programs.
 *
 * John D. Ramsdell
 * Copyright (C) 2004 The MITRE Corporation
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/time.h>
#include <lua.h>
#include <lauxlib.h>
#include <lualib.h>
#if defined HAVE_LIBREADLINE
#if defined HAVE_READLINE_READLINE_H
#include <readline/readline.h>
#endif
#if defined HAVE_READLINE_HISTORY_H
#include <readline/history.h>
#endif
#endif
#include "datalog.h"

#define STDIN_NAME "-"

#ifdef PACKAGE_NAME
const char package[] = PACKAGE_NAME;
#else
const char *package = NULL;
#endif

#ifdef VERSION
const char version[] = VERSION;
#else
const char version[] = "version unknown";
#endif

static void
print_version(const char *program)
{
  if (package != NULL)
    program = package;
  fprintf(stderr, "%s %s\n", program, version);
}

static void
usage(const char *prog)
{
  fprintf(stderr,
	  "Usage: %s [options] [file]\n"
	  "Options:\n"
	  "  -o file -- output to file (default is standard output)\n"
	  "  -i      -- enter interactive mode after loading file\n"
	  "  -l file -- load extensions written in Lua\n"
	  "  -p      -- print timing profile\n"
	  "  -t      -- print output as tab separated values\n"
	  "  -v      -- print version information\n"
	  "  -h      -- print this message\n"
	  "Use - as a file name to specify standard input\n",
	  prog);
}

uint64_t gettimestamp() {
    struct timeval tv;
    gettimeofday(&tv,NULL);
    return tv.tv_sec*(uint64_t)1000000+tv.tv_usec;
}

/* A datalog answer printer using datalog syntax. */

static int
print_answers_as_datalog(dl_answers_t a)
{
  int i, j, n;
  const char *p;
  size_t s;
  if (!a)
    return 0;
  n = dl_getpredarity(a);
  p = dl_getpred(a);
  s = dl_getpredlen(a);
  if (n == 0) {
    dl_putlconst(stdout, p, s);	/* Print zero arity predicate. */
    printf(".\n");
  }
  else if (n == 2 && !strcmp(p, "=") && s == 1) {
    for (i = 0; dl_getconst(a, i, 0); i++) {
      dl_putlconst(stdout, dl_getconst(a, i, 0),
		   dl_getconstlen(a, i, 0));
      printf(" = ");   /* Print equality answers in infix notation. */
      dl_putlconst(stdout, dl_getconst(a, i, 1),
		   dl_getconstlen(a, i, 1));
      printf(".\n");
    }
  }
  else {		 /* Print all other non-zero arity answers. */
    for (i = 0; dl_getconst(a, i, 0); i++) {
      dl_putlconst(stdout, p, s);
      printf("(");
      dl_putlconst(stdout, dl_getconst(a, i, 0),
		   dl_getconstlen(a, i, 0));
      for (j = 1; j < n; j++) {
	printf(", ");
	dl_putlconst(stdout, dl_getconst(a, i, j),
		     dl_getconstlen(a, i, j));
      }
      printf(").\n");
    }
  }
  dl_free(a);
  return 0;
}

/* A datalog answer printer using tab separated values. */

static int
print_answers_as_tab_separated_values(dl_answers_t a)
{
  int i, j, n;
  if (!a)
    return 0;
  n = dl_getpredarity(a);
  if (n == 0)
    printf("\n");		/* Print zero arity predicate. */
  else {			/* Print non-zero arity answers. */
    for (i = 0; dl_getconst(a, i, 0); i++) {
      dl_putlconst(stdout, dl_getconst(a, i, 0),
		   dl_getconstlen(a, i, 0));
      for (j = 1; j < n; j++) {
	printf("\t");
	dl_putlconst(stdout, dl_getconst(a, i, j),
		     dl_getconstlen(a, i, j));
      }
      printf("\n");
    }
  }
  dl_free(a);
  return 0;
}

/* Choose datalog answer printer. */

static int print_as_tsv = 0;

static int
print_answers(dl_answers_t a)
{
  if (print_as_tsv)
    return print_answers_as_tab_separated_values(a);
  else
    return print_answers_as_datalog(a);
}

/* Load a Datalog file. */

#define BUFFER_SIZE (1 << 10)

typedef struct {
  FILE *in;
  const char *filename;
  char buffer[BUFFER_SIZE];
} loadfile_t;

static const char *
getbuf(void *data, size_t *size)
{
  loadfile_t *lf = (loadfile_t *)data;
  FILE *in = lf->in;
  size_t n = fread(lf->buffer, 1, BUFFER_SIZE, in);
  if (n < BUFFER_SIZE && ferror(in)) {
    perror(lf->filename);
    exit(1);
  }
  *size = n;
  return n > 0 ? lf->buffer : NULL;
}

static void
loaderror(void *data, int lineno, int colno, const char *msg)
{
  loadfile_t *lf = (loadfile_t *)data;
  const char *filename = lf->filename;
  fprintf(stderr, "%s:%d:%d: %s\n", filename, lineno, colno, msg);
}

static int			/* Close all but stdin. */
leave(int rc, FILE *in)
{
  if (in != stdin)
    fclose(in);
  return rc;
}

static int
loadfile(dl_db_t db, FILE *in, const char *filename, uint64_t* load_done)
{				/* Read, evaluate, and print */
  int rc;			/* for a file. */
  dl_answers_t a;
  loadfile_t lf;
  lf.filename = filename;
  lf.in = in;
  rc = dl_load(db, getbuf, loaderror, &lf); /* Read. */
  if (load_done) {
    *load_done = gettimestamp();
  }
  if (rc)
    return leave(rc, in);
  rc = dl_ask(db, &a);		/* Eval. */
  if (rc)
    return leave(rc, in);
  return leave(print_answers(a), in); /* Print. */
}

/* Read a line of text for the interaction loop. */

#define LINE_SIZE (1 << 7)

typedef struct {
  dl_db_t db;
  int done;			/* Is current input complete? */
  int again;	/* Has some of current input already been returned? */
  int eof;			/* Was EOF found during reading? */
#if defined HAVE_LIBREADLINE
  char *buffer;
#else
  char buffer[LINE_SIZE];
#endif
} linebuffer_t;

static const char *
getaline(void *data, size_t *size)
{
  linebuffer_t *lb = (linebuffer_t *)data;
  char *buf;
  int nofiles = lb->again;
  char *prompt = lb->again ? ">> " : "> ";
  FILE *in;
  size_t n;
  if (lb->done)		     /* We're done, so return end of input. */
    return NULL;

  lb->again = 1;
  lb->eof = 0;

#if defined HAVE_LIBREADLINE
  lb->buffer = buf = readline(prompt);
#else
  fputs(prompt, stdout);	/* Show prompt */
  fflush(stdout);		/* then get a line */
  buf = fgets(lb->buffer, LINE_SIZE, stdin);
#endif

  if (!buf) {
    lb->done = 1;
    lb->eof = 1;		/* EOF or error found. */
    return NULL;
  }
  n = strlen(buf);
  if (n == 0) {			/* Cannot happen, right? */
    lb->done = 1;
    lb->eof = 1;
    return NULL;
  }
  else if (!nofiles && buf[0] == '=') {	/* File loading requested. */
#if !defined HAVE_LIBREADLINE
    if (buf[n - 1] != '\n') {	/* Line not finished. */
      fprintf(stderr, "file name too long\n");
      return NULL;		/* Give up. */
    }
    buf[n - 1] = 0;
#endif
    in = fopen(buf + 1, "r");	/* Only active at the beginning */
    if (!in)			/* of input--!nofile check.*/
      perror(buf + 1);
    else
      loadfile(lb->db, in, buf + 1, NULL);
    lb->done = 1;		/* Consider the current input */
    return NULL;		/* as containing no data. */
  }
#if !defined HAVE_LIBREADLINE
  else if (buf[n - 1] != '\n') { /* Line not finished. */
    lb->done = 0;		/* Continuation needed. */
    *size = n;
  }
  else if (n > 1 && buf[n - 2] == '\\') { /* Line continued. */
    lb->done = 0;		/* Lines that end in back slash */
    *size = n - 2;		/* are continued. */
  }
#else
  else if (buf[n - 1] == '\\') { /* Line continued. */
    lb->done = 0;		/* Lines that end in back slash */
    *size = n - 1;		/* are continued. */
  }
#endif
  else {			/* Complete input found, in other */
    lb->done = 1;		/* words, an unescapped newline */
    *size = n;			/* terminated input was found. */
  }
  return buf;
}

static void
lineerror(void *data, int lineno, int colno, const char *msg)
{
  (void)data; (void)lineno; (void)colno;
  fprintf(stderr, "%s\n", msg);
}

static int
interp(dl_db_t db)
{				/* Read, evaluate, and print */
  dl_answers_t a;		/* interaction loop. */
  int rc;
  linebuffer_t lb;
  lb.db = db;
  if (package != NULL)		/* Show welcome message. */
    printf("%s %s\n\n", package, version);
  do {
    lb.again = lb.done = 0;
    rc = dl_load(db, getaline, lineerror, &lb); /* Read. */
#if defined HAVE_LIBREADLINE
    if (lb.buffer && *lb.buffer)
      add_history(lb.buffer);
    free(lb.buffer);
    lb.buffer = NULL;
#endif
    if (!rc) {
      rc = dl_ask(db, &a);	/* Eval. */
      if (!rc) {
	if (print_answers(a))	/* Print. */
	  fprintf(stderr, "Internal error in print_answers");
      }
      else {
	fprintf(stderr, "Internal error in dl_ask\n");
	return 1;
      }
    }
  }
  while (!lb.eof);		/* Until EOF on input. */
  printf("\n");
  if (ferror(stdin)) {
    perror("interp");
    return 1;
  }
  else
    return 0;
}

int
main(int argc, char **argv)
{
  extern char *optarg;
  extern int optind;

  int interact = 0;

  int profile = 0;
  uint64_t dawn = 0;
  uint64_t eng_done = 0;
  uint64_t ext_done = 0;
  uint64_t qur_done = 0;
  uint64_t load_done = 0;
  uint64_t dusk = 0;

  char *input = NULL;
  char *output = NULL;
  char *lua = NULL;

  FILE *in = NULL;

  dl_db_t db;
  int rc;

  for (;;) {
    int c = getopt(argc, argv, "o:il:ptvh");
    if (c == -1)
      break;
    switch (c) {
    case 'o':
      output = optarg;
      break;
    case 'i':
      interact = 1;
      break;
    case 'l':
      lua = optarg;
      break;
    case 'p':
      profile = 1;
      break;
    case 't':
      print_as_tsv = 1;
      break;
    case 'v':
      print_version(argv[0]);
      return 0;
    case 'h':
      usage(argv[0]);
      return 0;
    default:
      usage(argv[0]);
      return 1;
    }
  }

  if (profile)
    dawn = gettimestamp();

  switch (argc - optind) {
  case 0:			/* Use stdin */
    interact = 1;
    break;
  case 1:
    input = argv[optind];
    if (strcmp(STDIN_NAME, input)) {
      in = fopen(input, "r");
      if (!in) {
	perror(input);
	return 1;
      }
    }
    else
      in = stdin;
    break;
  default:
    fprintf(stderr, "Bad arg count\n");
    usage(argv[0]);
    return 1;
  }

  if (output && !freopen(output, "w", stdout)) {
    perror(output);
    return 1;
  }

  db = dl_open();
  luaL_openlibs(db);
  if (!db) {
    fprintf(stderr, "Internal error\n");
    return 1;
  }

  if (profile)
    eng_done = gettimestamp();

  if (lua) {			/* Load Lua extensions if present  */
    rc = luaL_dofile(db, lua);
    if (rc) {
      const char *s = lua_tostring(db, -1);
      if (s)
	fprintf(stderr, "Error loading %s: %s\n", lua, s);
      else
	fprintf(stderr, "Failed to load %s\n", lua);
      return 1;
    }
  }

  if (profile)
    ext_done = gettimestamp();

  rc = 0;
  if (in) {
    rc = loadfile(db, in, input, &load_done);
    if (profile)
      qur_done = gettimestamp();
  }
  if (interact && !rc)
    rc = interp(db);
  dl_close(db);			/* Allow valgrind leak check. */

  if (profile) {
    dusk = gettimestamp();
    fprintf(stderr, "Total = %.2fms\n", (dusk - dawn) / 1000.0);
    fprintf(stderr, "Engine = %.2fms\n", (eng_done - dawn) / 1000.0);
    fprintf(stderr, "Extensions = %.2fms\n", (ext_done - eng_done) / 1000.0);
    fprintf(stderr, "Parsing = %.2fms\n", (load_done - ext_done) / 1000.0);
    fprintf(stderr, "Evaluating = %.2fms\n", (qur_done - load_done) / 1000.0);
  }
  return rc;
}
