<p></p> <!-- avoids duplicate title -->

Name resolution and type checking
=================================

Name resolution is the process of

* linking each name occurring in a program (e.g., `x`) with the
  declaration that introduces that name (e.g., a local variable
  declaration `var x: int`),

* linking each overloaded operator symbol (e.g., `+`) with the
  appropriate operator (e.g., integer addition or set union), and

* disambiguating syntactic constructs that cannot be distinguished by
  the parser (e.g., `A.B` may be one expression referring to a
  constant `B` in a module `A` or it may be a member-selection
  expression `.B` with a subexpression `A` denoting a local variable).

Name resolution reports an error if a name has no corresponding
declaration or if such a declaration cannot be determined uniquely.

Type checking is the process of

* computing or inferring types for all variables and subexpressions
  (e.g., for the statement `var x := 3;`, type checking may infer that
  the expression `3` and the local variable `x` both have type `int`),

* elaborating type parameters in calls (e.g., given `function
  Singleton<X>(x: X): set<X>`, a call `Singleton(3)` may be elaborated
  into `Singleton<int>(3)`), and

* checking that these types are used consistently (e.g., both operands
  of `&&` are boolean and the expression is used in a context where a
  boolean is allowed).

Type checking reports an error if the type constraints of the program
cannot be met (e.g., there is no type for `x` that makes `var x; x :=
3; x := false;` type check) or if the type constraints leave some
variables underspecified (e.g., the set element type of `x` in `var x
:= {};` is underspecified if `x` is not used anywhere).

Type checking depends on name resolution, since type checking needs to
know what names and operators are used in expressions. But name
resolution also depends on type checking (e.g., the type of expression
`e` is needed in order to resolve `M` in the member selection
`e.M`). This mutual dependence makes both name resolution and type
checking tricky.

General strategy
----------------

The general strategy breaks down as follows:

* Build the import relation among modules. Report an error if any
  cycles are detected.

* In topological order according to the acyclic import relation,
  process each module as follows:

    - Register the names of the top-level declarations of the module,
      linking each name with the declaration. Report an error for any
      duplicate name.

      "Registering a name" means putting it into a dictionary that
      maps the name to its declaration. There is such a dictionary for
      each name scope (module, type, block statement, etc.).

      Note that some declarations give rise to more than one name
      (e.g., a `class C` gives rise to the nullable type `C?` and the
      non-null type `C`, and a `least predicate P` gives rise to the
      least predicate `P` and the prefix predicate `P#`).

    - For each top-level type declaration that contains members (e.g.,
      a `class` or `datatype`), register the names of the members
      within the type. Report an error for any duplicate name. Note
      that some type declarations implicitly give rise to some other
      declarations (e.g., each constructor `Ctor` of a `datatype`
      gives rise to a discriminator member `Ctor?`, and a `class C`
      gives rise to two types, the nullable type `C?` and the non-null
      type `C`).

* Once the top-level and member names of a module have been
  registered, carry out the following steps, in order:

    - Resolve the types occurring in the signature of these
      declarations.
      (`ResolveTopLevelDecls_Signatures`)

      In most cases, every top-level declaration and member
      declaration explicitly lists the types in the declaration's
      signature. For example, a function declaration explicitly gives
      the types of its arguments and of its result type. However,
      there are three places among these declarations where types are
      optional:

          -- the base type of a `newtype` can be left implicit (e.g.,
             `newtype Byte = x | 0 <= x < 256`)
    
          -- the base type of a subset type can be left implicit (e.g.,
             `type Even = x | x % 2 == 0`)

          -- the type of a `const` declaration can be left implicit
             (e.g., `const pi := 3.14`)

      (Collectively, `newtype`s and subset types are called
      _redirecting types_.)

      Determining these types requires type inference, which will be
      done in a later step. For now, these missing types will be
      filled in as unique _type proxies_.

    - Detect and report an error for any cycle among type
      synonyms. More precisely, detect any cycle in the graph whose
      nodes are type synonyms declarations and where, for each
      declaration `type S = Rhs`, there is an edge `S` to every type
      synonym mentioned by name in `Rhs`.
      (`ResolveTopLevelDecls_Signatures`)
      
    - Detect and report an error for any cycle among redirecting
      types.  More precisely, detect any cycle in the graph whose
      nodes are redirecting types and where, for each redirecting-type
      declaration `T` with base type `B`, there is an edge from `T` to
      every redirecting type occurring in the type-synonym expansion
      of `B`.

      TODO: This cyclicity check currently considers only explicitly
      given base types `B`. That's bad (see
      https://github.com/dafny-lang/dafny/issues/2134).  It would be
      better done after doing type inference for these
      declarations. However, the cycles among explicitly given base
      types need to be detected before any further work can be done,
      so it seems this cyclicity check needs to be done twice.

    - For all other expressions and statements occurring in any
      top-level declaration or member declaration, one at a time,
      apply name resolution and type checking. Report any errors.
      More details about this below.

* To finish up, in several additional passes over the module's
  contents,

    - Compute ghost interests,
    
    - Discover bounds in comprehensions,
    
    - Build a call graph,
    
    - Check that the call-graph strongly connected component for a
      least predicate contains only least predicates, and similarly
      for greatest predicates, least lemmas, and greatest lemmas,
    
    - Enforce other usage rules (e.g., check that any function
      declared with `{:abstemious}` follows the appropriate rules).

Doing type checking
-------------------

