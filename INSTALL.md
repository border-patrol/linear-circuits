# Installing.

To build each of the languages, and execute their test suites,  needs to be installed first.

## Idris 2

# Building, Installing, and Playing

## Building

To build and use the languages presented we ask that you install [Idris2](https://www.idris-lang.org).
Information on obtaining Idris2 is publically available:

https://www.idris-lang.org/pages/download.html

Once Idris2 has been installed you can build each of the languages as:

#+begin_src bash
make netlist linear idealised
#+end_src

The build process shouldn't take too long, around one minute.

## Testing

The test suites can be ran using:

#+begin_src bash
make netlist-test-run linear-test-run idealised-test-run

#+end_src

and will take a moment or two to build and run.

## Installing

We have yet to add installation scripts or turn this into a serious tool to play with.
This might come later.

That being said, you can copy the binaries from `build/exec` to a well known location under `PATH` and you should be able to use them from there.

* Playing

The languages are presented as is, and type-checkers with a simple UX.
We do not provide anything fancy as our interest at the moment is in the tool itself and not necessarily its use by others.

There are examples in the directory called =tests=.


<!-- EOF -->
