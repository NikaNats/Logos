# Logos Formal Language Specification (Dogma)

Version: 1.0-draft
Status: Normative for language behavior; implementation-independent

This document defines the Logos language independently of any specific runtime, parser generator, or host language.
An implementation in Rust, C++, WASM, or Python should be able to conform to this specification without reading implementation source code.

## 1. Conformance Scope

A conforming implementation MUST provide:

- Lexical and syntactic acceptance/rejection consistent with the EBNF in this document.
- Expression precedence and associativity consistent with this document.
- Type compatibility and coercion behavior consistent with this document.
- Scope, shadowing, and mutation behavior consistent with this document.
- Tail-call trampoline behavior semantically equivalent to this document for eligible tail calls.

## 2. Lexical Conventions

### 2.1 Character Classes

- Letter = A-Z | a-z
- Digit = 0-9
- Underscore = _
- WordChar = Letter | Digit | Underscore

### 2.2 Identifiers

Identifier syntax:

- Identifier = (Letter | Underscore) , { WordChar }

This means:

- First character: letter or underscore
- Remaining characters: letters, digits, underscores

### 2.3 Literals

- Number literal: decimal integer or decimal floating literal (for example: 12, 12.5)
- String literal: double-quoted text on one line
- Boolean literals: Verily, Nay

### 2.4 Comments and Whitespace

- Whitespace is insignificant except as a token separator.
- Single-line comments are introduced by either # or // and continue to end-of-line.

### 2.5 Reserved Words

The following tokens are reserved as language keywords and MUST NOT be parsed as ordinary identifiers in keyword position:

- proclaim
- inscribe
- amend
- apocrypha
- mystery
- tradition
- as
- chant
- discern
- otherwise
- vigil
- confess
- icon
- contemplate
- aspect
- offer
- silence
- amen
- transfigure
- into
- supplicate
- write
- Verily
- Nay

## 3. Formal EBNF Grammar

The grammar below is normative and intentionally independent from parser implementation details.

```ebnf
Program         = { Statement } ;

Statement       = ProclaimStmt
                | InscribeStmt
                | AmendStmt
                | ApocryphaStmt
                | TraditionStmt
                | ChantStmt
                | DiscernStmt
                | VigilStmt
                | MysteryDefStmt
                | IconDefStmt
                | ContemplateStmt
                | OfferStmt
                | SilenceStmt
                | ExprStmt ;

ProclaimStmt    = "proclaim" , Expr , ";" ;
InscribeStmt    = "inscribe" , Identifier , [ ":" , TypeName ] , "=" , Expr , ";" ;
AmendStmt       = "amend" , Mutable , "=" , Expr , ";" ;
ApocryphaStmt   = "apocrypha" , StringLit , "mystery" , Identifier ,
                  "(" , [ Params ] , ")" , [ "->" , TypeName ] , ";" ;
TraditionStmt   = "tradition" , StringLit , [ "as" , Identifier ] , ";" ;
ChantStmt       = "chant" , Expr , Block , "amen" ;
DiscernStmt     = "discern" , "(" , Expr , ")" , Block , "otherwise" , Block , "amen" ;
VigilStmt       = "vigil" , Block , "confess" , Identifier , Block , "amen" ;
MysteryDefStmt  = "mystery" , Identifier , "(" , [ Params ] , ")" ,
                  [ "->" , TypeName ] , Block , "amen" ;
IconDefStmt     = "icon" , TypeName , "{" , { FieldDecl } , "}" , "amen" ;
ContemplateStmt = "contemplate" , "(" , Expr , ")" , "{" , CaseClause , { CaseClause } , "}" , "amen" ;
OfferStmt       = "offer" , Expr , ";" ;
SilenceStmt     = "silence" , ";" ;
ExprStmt        = Expr , ";" ;

Block           = "{" , { Statement } , "}" ;

FieldDecl       = Identifier , ":" , TypeName , ";" ;
Params          = Param , { "," , Param } ;
Param           = Identifier , [ ":" , TypeName ] ;

CaseClause      = "aspect" , Pattern , ":" , CaseBody ;
CaseBody        = Block | Statement ;
Pattern         = "_" | Expr ;

Expr            = Equality ;
Equality        = Comparison , { ("is" | "is" , "not") , Comparison } ;
Comparison      = Sum , { ("<" | ">" | "<=" | ">=") , Sum } ;
Sum             = Product , { ("+" | "-") , Product } ;
Product         = Unary , { ("*" | "/") , Unary } ;
Unary           = "-" , Unary
                | "transfigure" , Expr , "into" , TypeName
                | "supplicate" , Expr
                | Call ;

Call            = Access
                | Identifier , "(" , [ Args ] , ")" ;

Access          = Atom , { ("." , Identifier) | ("[" , Expr , "]") } ;
Mutable         = Identifier
                | Mutable , "." , Identifier
                | Mutable , "[" , Expr , "]" ;

Args            = Expr , { "," , Expr } ;
Atom            = NumberLit
                | StringLit
                | "Verily"
                | "Nay"
                | "[" , [ Expr , { "," , Expr } ] , "]"
                | "write" , TypeName , "{" , [ AssignList ] , "}"
                | Identifier
                | "(" , Expr , ")" ;

AssignList      = Assign , { "," , Assign } , [ "," ] ;
Assign          = Identifier , "=" , Expr ;

Identifier      = (Letter | "_") , { Letter | Digit | "_" } ;
TypeName        = Identifier ;
NumberLit       = Digit , { Digit } , [ "." , Digit , { Digit } ] ;
StringLit       = '"' , { StringChar } , '"' ;
```

## 4. Operator Precedence and Associativity

From highest binding to lowest:

1. Postfix access: . and []
2. Named call: f(args)
3. Unary: -, transfigure ... into ..., supplicate ...
4. Multiplicative: * /
5. Additive: + -
6. Relational: < > <= >=
7. Equality: is, is not

Associativity:

- Binary operators are left-associative.
- Parentheses override precedence.

Examples:

- 2 + 3 * 4 parses as 2 + (3 * 4)
- 9 - 3 - 2 parses as (9 - 3) - 2

## 5. Statement Termination Rules

Simple statements terminate with semicolon ;

- proclaim
- inscribe
- amend
- apocrypha
- tradition
- offer
- silence
- expression statement

Structured statements terminate with amen after their syntactic body:

- chant
- discern ... otherwise ...
- vigil ... confess ...
- mystery definition
- icon definition
- contemplate

## 6. Type System Semantics

## 6.1 Canonical Type Families

- Numeric: HolyInt, Int, HolyFloat, Float, Double
- Text: Text, String
- Boolean: Bool, Verily, Nay
- Sequence: Procession
- Void: Void, None
- Unknown runtime object category: Mystery

## 6.2 Runtime Type Classification

An implementation SHOULD classify runtime values into canonical type tags as follows:

- bool -> Bool
- integer -> HolyInt
- float -> HolyFloat
- string -> Text
- list/array -> Procession
- null/none -> Void
- other host object -> Mystery

## 6.3 Assignment Compatibility

Compatibility relation Compatible(declared, actual):

- Exact match is compatible.
- Float-family declared type accepts integer-family actual type.
- Text-family declared type accepts text-family actual type.
- Bool-family declared type accepts bool-family actual type.
- Numeric-family declared type accepts numeric-family actual type, except:
  - Int-family declared type does NOT accept float-family actual type.

Implications:

- HolyFloat <- HolyInt is valid.
- HolyInt <- HolyFloat is invalid.
- Text <- String is valid.
- Bool <- Verily/Nay is valid.

## 6.4 Binary Operator Result Typing

For +, -, *, /:

- Text + Text -> Text
- Numeric op Numeric -> Numeric result
- Division / over numeric operands -> HolyFloat
- For +, -, * over numeric operands:
  - if any operand is float-family -> HolyFloat
  - else -> HolyInt
- Other combinations are type errors.

For <, >, <=, >=:

- Numeric-only
- Result -> Bool
- Other combinations are type errors.

For equality (is, is not):

- Result type -> Bool
- Equality is defined for all operand categories at language level.

## 6.5 Icon Typing: Nominal Schema with Open Record Behavior

Icon declarations introduce named schemas of typed fields.
Construction by write IconName { ... } uses the selected icon schema.

Construction-time guarantees:

- For declared icon fields provided in the constructor, field values MUST satisfy declared field types.

Open record behavior (current Dogma):

- Omitted declared fields are allowed.
- Additional undeclared fields are allowed.

Assignment-level behavior:

- Variables declared with non-canonical type names (including icon names) accept Mystery-category runtime objects unless the implementation adds stronger nominal checks.

This means icon use is nominal at schema-selection time, but not fully nominally enforced at every assignment in the current language behavior.

## 6.6 Unknown and Mystery Fallback in Static/LSP Checking

Static analysis may produce Unknown when expression type cannot be inferred.
In current semantics:

- If static type is inferable and incompatible with declaration, report a type error.
- If static type is Unknown, checker MAY defer and avoid emitting mismatch solely from lack of information.

Runtime behavior remains authoritative:

- If runtime actual type is Mystery and declared type is canonical (numeric/text/bool/list/void), raise type mismatch.
- If runtime actual type is Mystery and declared type is non-canonical (for example icon name), runtime accepts value under current fallback semantics.

## 7. Execution and Memory Model

## 7.1 Environments and Scope

Execution uses:

- One global environment.
- A stack of local frames for function invocation and nested execution contexts.

Lookup rule:

1. Search local frames from innermost to outermost.
2. If not found, search globals.
3. If absent, raise unknown symbol error.

Declaration rule (inscribe):

- Declares in current local frame if one exists; otherwise in globals.

Assignment rule (amend):

- Mutates nearest existing binding in local frames or globals.
- If symbol does not exist, raise mutation error.

Shadowing:

- Local declarations may shadow globals and outer locals.
- Popping a frame restores visibility of shadowed bindings.

## 7.2 Argument Passing and Object Identity

Argument passing follows pass-by-sharing semantics:

- Immutable scalar values (numbers, booleans, strings) behave as value-like in practice.
- Procession and Icon values are mutable aggregates and are shared by reference identity.

Consequences:

- Mutating a Procession or Icon inside a callee mutates the same object visible to caller, unless implementation explicitly copies.

## 7.3 Icon and Procession Mutation Semantics

- Procession index mutation updates the underlying list object.
- Icon attribute mutation updates the underlying object map.
- Icon field-type checks apply when mutating declared fields of recognized icon instances.

## 7.4 Tail Call Optimization (TCO) Trampoline

Eligible tail calls:

- A call in direct tail-return position (offer f(...)) is trampoline-eligible.

Execution model:

- Instead of growing host call stack for each eligible tail call, runtime iterates in a loop carrying next function and arguments.

Deterministic guarantees:

- For programs where all recursion is trampoline-eligible, host recursion growth from those calls is bounded.
- Call outcome is deterministic relative to language semantics and side effects.

Non-guarantees:

- Non-tail recursive calls are not trampoline-optimized.
- Implementations may enforce safety limits on trampoline hops.
- External effects (FFI, host I/O timing, floating-point host behavior) can affect observable behavior outside pure expression semantics.

## 8. Implementation Notes (Informative)

This specification is intentionally parser/runtime agnostic.
An implementation may use recursive descent, parser generators, bytecode VMs, direct AST interpretation, or WASM execution, provided observable behavior remains conformant to this Dogma.
