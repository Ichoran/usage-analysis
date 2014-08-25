usage-analysis
==============

Bytecode analysis for Scala library usage

Goals are to be able to scan Jars to determine whether and how they use the Scala library.  A live copy of the library is assumed (so you can do reflection etc.).

In particular, you should be able to give it a classpath and package prefix and it will
 * Identify all public and protected classes, methods, and fields
 * Determine the inheritance hierarchy of those
to define what usage should be analyzed.  This defines the "source library".
 
Then, for each jar file (maybe directory paths also?) it will
 * Extract all bytecode
 * Find any inheritance from classes or traits in the source library
 * Determine whether methods/fields are from traits in the source library
 * Count usages of each constructor and method and field in the source library

Finally, it will provide summary statistics
 * Source-library-centric, showing what was used where
 * Target-centric, showing which parts used what bits of the source library

Note that this is not actually Scala-library-specific, but that's the only place I intend to test it (at this point at least).

It is Scala-specific, due to the need to avoid endless chatter from traits and closures.

It runs on bytecode instead of source to avoid caring about dependencies; you should be able to test any fragment of a project instead of needing all dependencies met in order to compile.
