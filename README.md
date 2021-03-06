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

There is also a work-in-progress `MethodOverrides` class that is runnable.
Try it with a first argument of `scala/collection/Traversable` followed by
the path to `scala-library.jar` followed by a list of other jars that may
override `Traversable` or its children within `scala-library.jar`.

### Preliminary Goals

[dbuild](https://github.com/typesafehub/dbuild) is a build tool that gathers and builds Scala projects,
and is used with a [large build set](https://github.com/scala/community-builds) to check the Scala compiler.

How completely does the community build set exercise the Scala library?  We would like to know
 * How many times each class in the Scala library is initialized
 * How many times each trait or class in the Scala library is inherited from
 * How many times each method in the Scala library is called (including those defined in traits)
 * How many times each method in the Scala library is overridden

To browse this data, we would like
 * A list of classes/traits sorted by times initialized
 * A list of classes/traits sorted by times inherited
 * A list of the top 200 methods used
 * A list of all methods never used
 * A list of top 200 methods overridden
 * Optionally, stats for the four things we'd like to know injected into Scaladocs.

Thus, with a single command, we can use the output of dbuild to generate a usage map for the Scala library.
(Or any other library, actually.)
