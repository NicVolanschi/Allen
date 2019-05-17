# Allen
A domain-specific language for context detection over binary sensors.

Allen [1, 2] is a domain-specific language (DSL) for programming context-aware applications. More precisely, for programming very concisely the detection logic of contexts (or situations) for such applications, over a set of binary sensors. (A binary sensor always produces two possible values, e.g. 0 and 1.)
Allen aims at simplifying the development of context recognition logic and making it more reliable.

Main concepts and features:
* Signal: a boolean function of (discrete) time. A signal models either the current state of a physical sensor or a higher-level context depending on such sensors. The "states" of a signal are the time intervals where the signal is 1.
* Semantics of an Allen program: based on the above model. Allows checking domain properties.
* Operators: allow to combine signals for deriving more complex signals. Each operator takes a given number of signals and produces a signal. For instance, the logic operators "and", "or", "not" have their usual meaning, at each time point, unary operators up(s) and down(s) produces the starting/ending events of signal s. Binary operator during(p,q) produces a signal consisting in the states of p entirely contained in some state of q.
* Parameterized operators: take, besides a given number of signals, a given number of scalar (numeric) parameters, such as temporal delays. For instance, the unary operators gt\[T\](s) and lt\[T\](s) produces signals consisting in the states of s which are longer/shorter than some delay T.
* Language constructs for defining new operators. For instance, "def up(s) = gt\[1\](s)" allows defining operator "up" above, based on the more primitive operator "gt". This feature enables the construction of user-defined abstractions, and thus creating layers of reusable pieces of context logic.
* Online context detection: the computation in real time of contexts based on incoming streams of events produces by sensors.

## WARNING
Allen is a research prototype. Its maintenance and roadmap may vary depending on research objectives that are continuously being redefined. Use it at your own risks. However, feel free to contact us if you are open to collaboration.

## Getting started

Allen consists of two executables, implemented as Perl scripts, available under directory src/:
* allenc: the Allen compiler. It compiles a source Allen file (extension ".aln") into a Perl module (extension ".pm"). For help on the compiler command and on the language, invoke it with no arguments.
* allen: the Allen virtual machine. It executes a set of contexts compiled from an Allen program on a log of events. For help on the VM command, and also on the format of the log file, invoke it with no arguments.

A quick start could be to run and inspect the examples under the ex/ subdirectory. Some of the most elaborated are in ex/smarthome/ and work on logs collected in real homes. Use the Makefile for reproducing the examples (e.g. cd ex/; make orange).

## References

[1] Nic Volanschi, Bernard Serpette, and Charles Consel.
"Implementing a Semi-causal Domain-Specific Language for Context Detection over Binary Sensors".
In GPCE 2018 - 17th ACM SIGPLAN International Conference on Generative Programming: Concepts & Experiences.

[2] Nic Volanschi, Bernard Serpette, Adrien Carteron, and Charles Consel.
"A Language for Online State Processing of Binary Sensors, Applied to Ambient Assisted Living".
In Proceedings of the ACM on Interactive, Mobile, Wearable and Ubiquitous Technologies, 2:4, 2018.
