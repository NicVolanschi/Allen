# Allen
A domain-specific language for context detection over binary sensors.

Allen is a domain-specific language (DSL) for programming context-aware applications. More precisely, for programming very concisely the detection logic of contexts (or situations) for such applications, over a set of binary sensors. (A binary sensor always produces two possible values, e.g. 0 and 1.)
Allen aims at simplifying the development of context recognition logic and making it more reliable.

NB: AllenRV is a reimplementation of Allen on Runtime Verification foundations.
Simply calling `allen -l rvlib.pm` instead of `allen` will override all native
operators with operators defined on top of LTL/MTL operators (see "rvlib.aln").

Main concepts and features:
* Signal: a boolean function of (discrete) time. A signal models either the current state of a physical sensor or of a higher-level context depending on such sensors. The "states" of a signal are the time intervals where the signal is 1.
* Semantics of an Allen program: based on the above model. Allows checking domain properties.
* Operators: allow to combine signals for deriving more complex signals. Each operator takes a given number of signals and produces a signal. For instance, the logic operators "and", "or", "not" have their usual meaning, at each time point, unary operators up(s) and dn(s) produces the raising/falling events of signal s. Binary operator during(p,q) produces a signal consisting in the states of p entirely contained in some state of q.
* Parameterized operators: take, besides a given number of signals, a given number of scalar (numeric) parameters, such as temporal delays. For instance, the unary operator delay[T](s) produces the signal s delayed by T; operators s > T and s < T produce signals consisting in the states of s which are longer/shorter than some delay T.
* Language constructs for defining new operators. For instance, "def up(s) = s & ~delay[1](s)" allows defining operator "up" above, based on more primitive operators. This feature enables the construction of user-defined abstractions, and thus creating layers of reusable pieces of context logic.
* Online context detection: the computation in real time of contexts based on incoming streams of events produces by sensors.

## WARNING
Allen is a research prototype. Its maintenance and roadmap may vary depending on research objectives that are continuously being redefined. Use it at your own risks. However, feel free to contact us if you are open to collaboration.

## Installation

No installation is required. You only need Perl with its core modules installed.
Allen has been tested on Perl versions 5.18-5.28 on Linux and MacOS X, but
should work on other configurations as well.

## Getting started

Allen consists of two executables, implemented as Perl scripts, available under directory src/:
* allenc: the Allen compiler. It compiles a source Allen file (extension ".aln") into a Perl module (extension ".pm"). For help on the compiler command and on the language, invoke it with no arguments.
* allen: the Allen virtual machine. It executes a set of contexts compiled from an Allen program on a stream or log of events. For help on the VM command, and also on the format of the input and output files, invoke it with no arguments.
There are also some library source files, mainly implementing the signal operators, either in Perl (e.g. builtins.pl) or in Allen itself (e.g. rvlib.aln).

A quick start could be to run and inspect the examples under the ex/ subdirectory. Some of the most elaborated are in ex/smarthome/ and work on logs collected in real homes. Use the Makefile for reproducing the examples (e.g. cd ex/; make orange).

## Documentation

[1] Nic Volanschi and Bernard Serpette.
"AllenRV: an Extensible Monitor for Multiple Complex Specifications with High Reactivity ---
Extended version".
Extended version of [2], including a short programming tutorial as an Appendix.
http://nic.volanschi.free.fr/papers/allen-rv19-extended.pdf

[2] Nic Volanschi and Bernard Serpette.
"AllenRV: an Extensible Monitor for Multiple Complex Specifications with High Reactivity".
In RV'19 - The 19th International Conference on Runtime Verification.

[3] Nic Volanschi, Bernard Serpette, and Charles Consel.
"Implementing a Semi-causal Domain-Specific Language for Context Detection over Binary Sensors".
In GPCE 2018 - 17th ACM SIGPLAN International Conference on Generative Programming: Concepts & Experiences.

[4] Nic Volanschi, Bernard Serpette, Adrien Carteron, and Charles Consel.
"A Language for Online State Processing of Binary Sensors, Applied to Ambient Assisted Living".
In Proceedings of the ACM on Interactive, Mobile, Wearable and Ubiquitous Technologies, 2:4, 2018.
