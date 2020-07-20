## Datalog

This repo has been forked from [MTRE Datalog](http://datalog.sourceforge.net/datalog.html). Some changes include:
1. Allow `:` in identifier names as rudimentary "namespace" support
2. Extensional Lua extensions allowed when creating primitives
3. Stratified negation added with `\+` syntax
4. Removed the embedded Lua. Lua is now an external dependency

### Abstract

This package contains a lightweight deductive database system.
Queries and database updates are expressed using Datalog--a
declarative logic language in which each formula is a function-free
Horn clause, and every variable in the goal of a clause must appear in
the body of the clause.  The use of Datalog syntax and an
implementation based on tabling intermediate results, ensures that all
queries terminate.

The components in this package are designed to be small, and usable on
memory constrained devices.  The package includes an interactive
interpreter for Datalog, and a library that can be used to embed the
interpreter into C programs.

### Installation

Please read `INSTALL2` before proceeeding.

Install using the usual `./configure; make; make install` sequence as
described in the file INSTALL.

If you have Lua 5.2 installed, configure with the --with-lua option.
On Debian-based systems, use:

```
    $ ./configure --with-lua-suffix=5.2 CPPFLAGS=-I/usr/include/lua5.2
```

Datalog can be built on top of Lua 5.1 too.

### Documentation

This package is documented using Texinfo and a manual page.  The NEWS
file contains a history of user-visible changes.  The ChangeLog
records changes to the package.

### Test Suite

The source distribution contains examples of Datalog programs used for
testing that are not installed.  Examples from the Texinfo manual are
also included.
