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

### Compilation notes

Use sbt.  For now, you need to manually place the complete ASM5 jar in lib.

### Completeness notes

Very rough.  Can read source and target libraries (via calls to methods on `scasm.Usage` object.  A few methods are provided to inspect what is read.

For a simple example, `val lib = scasm.Usage.source("/jvm/scala/lib/scala-library.jar", true).right.get` from the REPL / sbt console.  (Assuming that this path is where you keep a scala-library.jar.)

Interesting methods on the returned `Lib` instance include `ancestry`, `descendants`, and `methods.callgraph`.  None of them are probaby comprehensible yet, however.

