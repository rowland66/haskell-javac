# haskell-javac
A primitive Java compiler written in Haskell

Haskell-javac is a recreactional project that I have worked on while reading 'Types and Programming Languages' by Benjamin C. Pierce. The initial goal of the project was to improve my understanding of some of the concepts in the book by implementing a feather weight Java that the book describes, and to imporove my Haskell.

The Haskell-javac compiler compiles a subset of Java called feather java. Feather Java supports the following features:

1. Classes only with no support for interfaces.
1. All variables are reference types (no primitives)
2. Constructors must assign values all class fields. No null values.
3. Constructors can only invoke parent constructors (super), other constructors (this), and assign values to fields. No expression evaluation in constructors
3. Methods must return a value (no void returns), and are limited to a single Java expression.
4. Supported literal are String, Integer and Boolean.
5. Boxing and Unboxing of Integer and Boolean classes is supported.
6. Conditional expressions are supported.

The haskell-javac compiler supports 3 command line parameters:

1. -d indicates the output directory for the compliled classes
2. -cp indicates the classpath to search for referenced classes during compilation. Even JDK classes need to be provided on the classpath. Directories only, jar files are not supported.
3. -v dump the abstract syntax tree on type checking errors