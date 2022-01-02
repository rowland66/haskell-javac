# haskell-javac
A primitive Java compiler written in Haskell

Haskell-javac is a recreactional project that I have worked on while reading 'Types and Programming Languages' by Benjamin C. Pierce. The initial goal of the project was to improve my understanding of some of the concepts in the book by implementing a feather weight Java that the book describes, and to imporove my Haskell.

The Haskell-javac compiler compiles a subset of Java called feather java. Feather Java supports the following features:

1. Classes only with no support for interfaces.
1. All variables are reference types (no primitives)
2. Constructors must assign values all class fields. No null values.
3. Constructors can only invoke parent constructors (super) and assign values to fields.
3. Methods must return a value, and are limited to a single Java expression.
4. Supported literal are String, Integer and Boolean.
5. Boxing and Unboxing of Integer and Boolean classes is supported.

The haskell-javac compiler supports 2 command line parameters:

1. -d indicates the output directory for the compliled classes
2. -cp indicates the classpath to search for referenced classes during compilation. Directories only, jar files are not supported.
