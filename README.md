# Dusk Programming Language

A minimal programming language for game development.

Dusk is designed with a small, but powerful set of core language constructs. It features a a precise, stop-the-world, mark-and-sweep garbage collector for memory management.

It also includes builtin functions for all the necessities of game programming, including a 2d/3d runtime built on top of OpenGL known as "Sulfur".

This write-up documents the (intended) syntax, and semantics of Dusk, which is still in the early stages of development.

## Table of Contents

1. [Compiler Usage](#compiler-usage)
1. [Datatypes](#datatypes)
1. [Expressions and Statements](#expressions-and-statements)
1. [Functions and Declarations](#functions-and-declarations)

## 1. Compiler Usage

`TODO:` Keep up-to-date with actual Dusk compilation options.

```
dusk <directory>
-o Name of the output executable.
-w Sets compilation to compile with mingw and target Windows.
-t Specifies a target architecture for the executable.
-r The directory in which the compiler's runtime is stored.
-help Display a list of compilation options.
```

## 2. Datatypes

### 2.1 Primitive Datatypes

#### Numerics and Booleans

Dusk has one signed integer type `Int`, one 32-bit floating-point type `Float`, and three unsigned integer types `U8`, `U32`, and `U64`.

Integer literals may be written in decimal or hexadecimal notation. Appending an `l` or `L` to an integer literal will make it an (unsigned) 64-bit integer (`U64`). Similarly `b` or `B` is used to write `U8` literals, and `u` or `U` is used for `U32` literals.
```
2, 1023, -64        -- decimal
0x3A, 0xbb          -- hexadecimal
999l, 10000000000L  -- 64-bit integer
1b, 251B            -- 8-bit integer
4000u, 65535U       -- 32-bit integer
```

Hex literals for `U64`, `U8`, and `U32` integers can be written using `0l`, `0b`, and `0u` respectively.
```
0lF0F8000000098C    -- 64-bit hex
0bA0                -- 8-bit hex
0uFFA0C0            -- 32-bit hex
```

Float literals are written by including a decimal point anywhere in a number. Scientific notation is also available.
```
3.0, 609.       -- float
1.3e4, 766.E10  -- scientific notation
```

Dusk also has booleans of type `Bool`, with two literals:
```
true
false
```

`TODO:` Implement all literal types.

#### Characters and Strings

In Dusk unsigned 8-bit integers also double as ASCII characters that may be written using character literals with single quotes Ex: `'b'`. The following escape sequences may be used:

| Escape Sequence | ASCII | Description |
|:-----|:-------|:----------------------|
| `\0` | `0x00` | Null |
| `\a` | `0x07` | Bell |
| `\b` | `0x08` | Backspace |
| `\t` | `0x09` | Tab |
| `\n` | `0x0A` | New Line |
| `\v` | `0x0B` | Vertical Tab |
| `\f` | `0x0C` | Form Feed |
| `\r` | `0x0D` | Carriage Return |
| `\"` | `0x22` | Double Quote |
| `\'` | `0x27` | Single Quote |
| `\\` | `0x5C` | Backslash |
| `\xNN` | `0xNN` | - |

Operations available on integers are generally available for characters as well, where they are treated as unsigned 8-bit integers.

Dusk also has a `String` type - a heap-allocated sequence of characters. They are written using double quotes Ex: `"Hello world!"`.
```
"Hello world!"
"\"The quick brown fox\n jumps over the lazy dog.\""
```

#### Object IDs

All heap-allocated objects in Dusk have a unique "object id" of type `OID` identifying them which may be used for shallow equality of objects. (It is essentially the object's pointer value, but pointer arithmetic cannot be performed on it).

There are no literals to manually initialize an oid. An object's oid may be obtained using field syntax.

Ex:
```
obj.oid
```

`TODO:` Implement OIDs.

### 2.2 Operators

From highest to lowest precedence, the following unary and binary operators are available in Dusk:
```
-- unary operators
|_|         
-   !   ^

-- arithmetic operators
**
*   /    /.   %
+   -

-- bitwise operators
<<  >>
^
&
|

-- comparison / boolean operators
=   !=   <    <=  >   >=
&&
||
```

All binary operators are left-associative.

These operators have their standard meaning along with `**` for exponentiation, `/.` for floating-point division (distinct from `/` truncating division), the standard bitwise operators `<<`, `>>`, `&`, `|` with `^` overloaded for both bitwise negation and bitwise XOR, and the unary `measure` operator `|_|` used for things like the absolute value, the length of a string, and later the size of arrays.

These operators may also be called as normal functions using their "explicit name", and they may be overloaded using this explicit name as well. A complete table of operators, explicit names, and what overloads are built-in to the language is given below:

| Operator | Explicit Name | Builtin Overloads | Description |
|:---------|:--------------|:------------------|:------------|
| `-` (Unary) | `neg` | `Int`, `Float` | Numeric negation |
| `+` | `add` | `Int`, `U8`, `U32`, `U64`, `Float`, `String` | Numeric addition/String concatenation |
| `-` | `sub` | `Int`, `U8`, `U32`, `U64`, `Float` | Numeric subtraction |
| `*` | `mul` | `Int`, `U8`, `U32`, `U64`, `Float` | Numeric multiplication |
| `/` | `div` | `Int`, `U8`, `U32`, `U64` | Truncating numeric division |
| `/.` | `flDiv` | `Int`, `U8`, `U32`, `U64`, `Float` | Numeric division |
| `%` | `mod` | `Int`, `U8`, `U32`, `U64` | Numeric modulo/remainder |
| `**` | `expo` | `Int`, `U8`, `U32`, `U64`, `Float` | Numeric exponentiation |
| `=` | `equals` | `Int`, `U8`, `U32`, `U64`, `Float`, `Bool`, `String`, `OID` | Value Equality |
| `!=` | `neq` | `Int`, `U8`, `U32`, `U64`, `Float`, `Bool`, `String`, `OID` | Value Inequality |
| `<` | `lt` | `Int`, `U8`, `U32`, `U64`, `Float` | Less than comparison |
| `<=` | `leq` | `Int`, `U8`, `U32`, `U64`, `Float` | Less than or equal comparison |
| `>=` | `gt` | `Int`, `U8`, `U32`, `U64`, `Float` | Greater than comparison |
| `>=` | `geq` | `Int`, `U8`, `U32`, `U64`, `Float` | Greater than or equal comparison |
| `!` (Unary) | `not` | `Bool` | Logical negation |
| `&&` | `and` | `Bool` | Logical conjunction |
| `||` | `or` | `Bool` | Logical disjunction |
| `|_|` (Unary) | `measure` | `Int`, `Float`, `String` | Absolute value/String length |
| `^` (Unary) | `bitNeg` | `Int`, `U8`, `U32`, `U64`, `Float` | Bitwise complement |
| `<<` | `bitShiftLeft` | `Int`, `U8`, `U32`, `U64`, `Float` | Bitwise shift left |
| `>>` | `bitShiftRight` | `Int`, `U8`, `U32`, `U64`, `Float` | Bitwise shift right |
| `&` | `bitAnd` | `Int`, `U8`, `U32`, `U64`, `Float` | Bitwise AND |
| `|` | `bitOr` | `Int`, `U8`, `U32`, `U64`, `Float` | Bitwise OR |
| `^` | `bitXor` | `Int`, `U8`, `U32`, `U64`, `Float` | Bitwise XOR |

Note that the `=`/`equals` function is NOT defined for all types. In fact for most types it is undefined, and must be explicitly defined. Shallow equality for heap-allocated data structures is performed through their OIDs.

`TODO:` Implement all operators/overloads.

### 2.3 Math / Misc Functions

#### Math

Dusk includes the following builtin math functions:

| Function Name | Builtin Overloads | Description |
|:--------------|:------------------|:------------|
| `sqrt` | `Float` | Square Root |
| `log` | `Float` | Logarithm |
| `log10` | `Float` | Log Base-10 |
| `ln` | `Float` | Natural Log |
| `sin` | `Float` | Sine |
| `cos` | `Float` | Cosine |
| `tan` | `Float` | Tangent |
| `asin` | `Float` | Inverse Sine |
| `acos` | `Float` | Inverse Cosine |
| `atan` | `Float` | Inverse Tangent |
| `atan2` | `Float` | Angle from `x`, `y` Coordinates |
| `toInt` | `U8`, `U32`, `U64`, `Float` | Truncation/Cast/Round to zero |
| `toU8` | `Int`, `U32`, `U64`, `Float` | Truncation/Round to zero |
| `toU32` | `Int`, `U8`, `U64`, `Float` | Truncation/Cast/Round to zero |
| `toU64` | `Int`, `U8`, `U32`, `Float` | Cast/Round to zero |
| `toFloat` | `Int`, `U8`, `U32`, `U64` | Cast |
| `round` | `Float` | Round to nearest integer |
| `floor` | `Float` | Mathematical floor to integer |
| `ceil` | `Float` | Mathematical ceiling to integer |
| `toDegrees` | `Float` | Radian to degree conversion |
| `toRadians` | `Float` | Degree to radian conversion |

Constants `_PI` and `_E` are also available.

`TODO:` Implement all math functions/overloads.

#### String Operators / Functions

In addition to string literals, strings may be initialized using arrays of characters (`U8` values):
```
new String(new 1d['M', '4', 'R', 'I', '0'])
```

(More details on array syntax will be given later in this section).

Individual characters may be read out of a string using array syntax:
```
var s = "September."
print(toString(s[3]))    -- prints 't'
```

Lastly, Dusk implements two builtin string functions:
| Function Name | Builtin Overloads | Description |
|:--------------|:------------------|:------------|
| `toString` | `Int`, `U8`, U32`, `U64`, `Float` | Convert to String |
| `subString` | `String` | Substring operator |

### 2.4 Enums

In addition to the primitive types, Dusk allows for the definition of custom "enum" values.

Enumeration types are explicitly defined using the `enum` keyword:

```
enum WeekDay = Sun | Mon | Tue | Wed | Thur | Fri | Sat
```

The `is` and `isnt` keyword may be used on an enum value to determine which enum is being used.
Note that the `=` operator is NOT defined in general for enums (although it may be explicitly defined and overloaded if desired).

Ex:
```
var v = Sun
if b then v = getDayOfWeek() end
if v is Tue then
  doTuesdaySpecial()
elsif v isnt Sun && v isnt Sat then
  doWork()
end
```

Each case in an enum is "enumerated" and assigned an integer starting from `0`. This raw integer may be obtained using the `.i` operator.

Ex:
```
enum SpringMonth = March | April | May | June
print(March.i)   -- prints 0
var z = May
print(z.i + 2)   -- prints 4
```

The opposite is also true, an integer may be used to create an enum value using the type name as a constructor.

Ex:
```
var m = SpringMonth(3)
print(nameOfMonth(m))    -- prints "June"
```

`TODO:` Sometimes it is useful to have an enum definition skip numbers in the enumeration. Cases in the enum definition may be explicitly assigned an integer, skipping over the preceding values in the sequence and continuing from there.

Ex:
```
enum KeyEnum =
  KeyNull | KeySOH
  | KeySpace[32] | KeyExclam
  | KeyA[65] | KeyB | KeyC | ...
printInt(KeySOH.i)      -- prints 1
printInt(KeySpace.i)    -- prints 32
printInt(KeyExclam.i)   -- prints 33
```

Attempting to go backwards in the enumeration will result in an error.

#### Enum Attributes

It's often useful to map enums to different values for each case. Dusk allows this through the use of  "attribute" syntax.

```
enum WeekDay attrs { String s } =
  Sun{ "Sunday" }
  | Mon{ "Monday" }
  | Tue{ "Tuesday" }
  | Wed{ "Wednesday" }
  | Thu{ "Thursday" }
  | Fri{ "Friday" }
  | Sat{ "Sunday" }
```

Note that enum attributes must be given constant values. This allows enum attributes to be implemented without increasing their memory footprint as a lookup in a constant table.

This attribute can then be accessed using `.` syntax, as if it were a struct field.

Ex:
```
var d = Mon
if b then d = yesterday() end
print(d.s)
```

### 2.5 Tuples

Dusk's most basic aggregate type is the tuple type. Tuples are immutable, fixed-size lists of values (of possibly differing types). They may, for example, be used as the return type for a function returning multiple values. They are not heap-allocated, and thus care should be taken with using them to represent large objects.

Examples of tuple literals and their types include:
```
(16, false)        -- type (Int, Bool)
(4, "hello", 123)  -- type (Int, String, Int)
```

Tuples may be indexed using the `.` symbol, followed by a (`1`-indexed) number indicating which tuple field to read from.

Ex:
```
pair.2
pairTriple.1.3
```

Tuples are immutable, and so there are no operators for writing to a tuple.

#### Pattern Variable Declaration

The `var` keyword can be used to bind the elements of a tuple to variables in one step through the use of tuple "patterns". Rather than having `var` followed by an identifier, we have `var` followed by a tuple of identifiers, or `_` wildcard spaces (for elements that we wish to ignore).

Ex:
```
var (r, g, _) = color
```

Note that tuple patterns cannot be nested (nested tuples are considered to be un-idiomatic).

### 2.6 Arrays and Tensors

Dusk also has mutable, variable-size lists in the form of arrays. Arrays are heap-allocated, and function like "vectors" in other languages (they may be resized in-place).

Dusk also supports multi-dimensional arrays, known as "tensors". The type of an array is written with the dimensionality of the array, followed by the type of value contained by the array.

Ex:
```
1d[String]
1d[(Float, Bool)]
2d[Tile]
5d[Float]
```

#### Arrays

Array literals are declared using the `new` keyword (which is used in general for initializing heap-allocated values). Examples of 1-dimensional array literals include:
```
new 1d[1, 2, 3, 4, 5, 6]
new 1d[~String]    -- initializes an empty array of the given type
```

Arrays may also be initialized using "array format" syntax, which initializes an empty array up to a given size and fills it with values.

Ex:
```
new 1d(6)[.. 0]
new 1d(n + 1)[.. newFoo()]
```

Arrays may be resized and re-formatted using similar syntax.
```
reformat a(8)[.. emptyTile()]
```

`TODO:` Implement re-formatting syntax.

Arrays may be indexed and updated using fairly standard syntax:
```
return a[x + 1]   -- array lookup
b[i] = z ** 2     -- array update
```

#### Tensors

Tensor literals have syntax similar to regular 1d array literals, however unless the array is empty, they require dimensions which specify how to lay out the data.

Ex:
```
new 2d[4, 4][
  1, 0, 0, 0
  0, 1, 0, 0
  0, 0, 1, 0
  0, 0, 0, 1
]
new 3d[~Float]
```

Tensors may also be initialized and resized using formatting syntax.
```
new 2d(10, 20)[.. newTile()]
reformat aaa(100, 100, 100)[.. 0]
```

Tensors data is stored in row-major order, and they are indexed accordingly using a comma separated set of integers as the index. For example:
```
var a = new 2d[3, 2][
  0, 1, 2,
  3, 4, 5
]
return a[0, 1]   -- returns 3
```

### 2.7 Structs

Tuples, and Arrays are accessed through integer indices. Structs are heap-allocated, mutable data structures accessed through a fixed set of field identifiers.

Struct types, must be explicitly named using the `struct` keyword.

Ex:
```
struct Box{
  Int x,
  Int y,
  Int width,
  Int height
}
```

Structs are initialized using the `new` keyword and must have all their fields explicitly initialized.

Ex:
```
new Box{ x = 0, y = 0, width = 16, height = 16 }
```

Struct fields may be indexed and updated using the field identifier.

Ex:
```
return box.x + box.width   -- struct read
box.y = box.y + gravity    -- struct update
```

### 2.8 Unions

Tuples, arrays, and structs all define datatypes with a fixed structure. Dusk also allows for datatypes with a varying structure, using an enum to identify structural variants. We call such a data structure a "union".

Unions are defined using the `union` keyword as either a union of tuples or union of structs. These tuple/struct cases are combined with an enum used to distinguish each case, known as the union "tag".

Ex:
```
union TileType = None | Solid(Int) | Water(Int, Float) | Lava

union WordTree =
  Leaf{ String word }
  | Branch{ String word, WordTree left, WordTree right }
```

Note that unions of tuples, like regular tuples, are not heap-allocated. As a result, they cannot be recursive. Recursive unions must be unions of structs.

`TODO:` Implement struct unions.

#### Type Narrowing

The `is` and `isnt` keyword may be used on a union value to check the tag.

Ex:
```
if grid[i, j].tileType is Lava then
  doBurn()
elsif grid[i, j].tileType isnt Solid then
  doSomething(v)
end
```

Once the tag of a variable containing a union is known, it may be treated as if it was a tuple / struct of the corresponding case, which we call "type narrowing." Crucially, the data inside may be indexed or unpacked using standard tuple / struct notation.

Ex:
```
if v is Solid then
  x = v.1
elsif v is Water then
  var (_, f) = v
  foo(f)
end

if d is Branch then
  traverse(d.left)
  traverse(d.right)
end
```

Importantly, type narrowing is only applicable to unions stored directly in variables and NOT to unions accessed through structs or other data structures.

Ex:
```
if a is Solid then
  checkVal(a.1)              -- this works
end
if grid[i, j] is Water then
  checkVal(grid[i, j].1)     -- this does NOT work
end
```

This is because of limitations in type narrowing analysis. Even for a variable, the type narrowing may be invalidated if that variable is later mutated.

Ex:
```
if v isnt Solid then
  return
end
var a = foo(v.1)     -- this works
if a < 0 then
  v = regen()
end
var b = foo(v.1)     -- this does NOT work
```

On the other hand, type narrowing has robust enough case analysis to recognize a case based on negation, or based on exhaustive case analysis. For example, the following is valid:

```
union Story = A(Int, Int) | B(Int, Int, Int) | C(Float)

fn f(Story s) Int
  if s is B then return s.2 + s.3 
  elsif s isnt A then return floor(s.1) end
  return s.2
end
```

#### Implicit Enums

The tag of a union may also be explicitly accessed using the `.t` operator.

Ex:
```
var v = Water(4.67)
v = flood(v)
if v.t.i = 2 then print(v) end
```

Union types implicitly define a corresponding enum type for the union's tag value. This enum type is named by adding `.t`, and values of this enum type can be constructed using the `@` symbol.

For example, the above example essentially defines enum types where:
```
enum TileType.t = @None | @Solid | @Water | @Lava
enum WordTree.t = @Leaf | @Branch
```

### 2.10 Nullables

Sometimes it is useful to allow "null" pointers, for instance in an array where most of the entries will should be empty. To interact with such values safely, we introduce a notion of a nullable datatype.

A (heap-allocated) datatype may be designated as nullable using a `?` symbol.

Ex:
```
String?
Tile?
1d[String]?
```

Note that his may only be done for heap-allocated is important. Primitive datatypes must be explicitly boxed/unboxed if this behavior is desired (although it is usually better to designate an enum for this purpose).

`TODO:` Include error-handling for attempting to null non-heap datatypes.

Null literals use the keyword `null`, with an optional type annotation. The type annotation may be useful because Dusk does not have type inferencing, and expressions are expected to have a definite type in variable declarations and array initializers.

Ex:
```
null
null[~FooBar]
```

When checking whether a value is `null`, the `is` keyword should be used. Type narrowing for unions also applies to nullable values - once a nullable variable has been confirmed to be non-null, the underlying type may be used normally.

Ex:
```
var g = null[~Fraction]
g = calc(e)
if g isnt null then
  printInt(g.denominator)
end
```

## 3. Expressions and Statements

### 3.1 Identifiers

Identifiers are a sequence of letters, numbers, and underscores that:
- Begin with a letter, or single underscore (with at least one letter).
- Do not match any reserved keywords.

Identifiers are split into three categories:
- Constant identifiers if the first character is an underscore, and every letter is capitalized.
- Type/constructor identifiers if the first letter is capitalized.
- Variable/miscellaneous identifiers otherwise.

```
_COLORS, _TBL_XL     -- Constant identifiers
Int, _Foo32_xx       -- Type identifiers
x, _barZ_52          -- Variable identifiers
```

### 3.2 Variable Declaration/Assignment

The `var` keyword is used to declare new variables. Once declared, the `=` symbol is  used to re-assign the value stored in a variable.

Ex:
```
var x = 90
var y = "Test"
var z = f(x, y) ** 2 + 1
x = x + 1
y = "Tset"
```

### 3.3 Function Calls

Functions may be called in a standard way, with the function name surrounded by a comma-separated list of expressions wrapped in parentheses.

Ex:
```
foo()
bar(0, "Hello", 3.6)
```

Functions are often used in expressions for variable declarations/assignments, but they may also be called as standalone statements within a function body when they perform some side-effect.

Functions may also be called using "object call syntax", where the first argument is put in front, and the remainder of the function is treated as a method of the first argument. Note that this is just syntactic sugar for the normal function call syntax.

Ex:
```
obj.f(x, y)
--- is equivalent to
f(obj, x, y)

a.g()
--- is equivalent to
g(a)
```

Dusk does not have classes/objects, but this syntax is available to imitate object-like syntax when appropriate.

### 3.4 Return Statements

The `return` keyword is used within a function to terminate execution and (when applicable) return a value to the function caller.

The `return` keyword may be used on its own, or with an expression after it.

Ex:
```
return
return 9
return foo(x) + bar(a, z)
```

### 3.5 Code Blocks

Multiple statements may be sequenced together in code blocks.

Ex:
```
var i = 0
j = read()
i = i ** j
convolve(i, j)
```

Note that code blocks do not require separators between statements, not even newlines. This means that the following type of code is valid (although in poor style):

```
var a = 1
var b = a + 1 a = a + 1
c = b * a a = a + 2
```

### 3.6 Conditionals

Dusk also has branching `if`-`else` conditionals, with the `elsif` available to include additional branches. Conditionals need not have a final `else` branch.

Ex:
```
if x < 1 then
  print("A")
end

if a = 0 then
  x = foo()
elsif a = 1 then
  y = bar()
else
  z = 99
end
```

### 3.7 Loops

Dusk has two main kinds of loops. First it has simple `while` loops, which repeat a block of code until a certain condition is met.

Ex:
```
while x > 0 do
  sum = sum + x
  x = x - 1
end 
```

The `loop` keyword exists as syntactic sugar for a loop where the condition is always true (for loops that only break through the use of a `return` statement, or code that is intended to run indefinitely).

Ex:
```
loop
  x = doSomething()
  draw(0, 0, "Test: " + toString(x))
end
```

The second main type of loop that Dusk has are `for` loops.

For loops themselves come in two flavors. First, we have for loops that iterate through a sequence of numbers from `0` to `n`, either inclusive or exclusive.

Ex:
```
-- exclusive case
for i < 10 do
  print(toString(i) + "\n")
end

-- inclusive case
for j <= 10 do
  sum = sum + j
end
```

Second, we have for loops that iterate directly through the elements of either arrays or dictionaries using the `in` keyword.

Ex:
```
for v in a do
  update(v)
  draw(v)
end
```

The syntax that describes the method of iteration for a for loop is known as its "range". A for loop may have multiple ranges, which is used as syntactic sugar for a set of nested for loops.

Ex:
```
for i < width, j < height do
  draw(a, i, j)
end 
```

Note that the first range given (in this case `i < width`) will be unrolled to be the innermost loop. (This is to match the layout of multi-dimensional arrays, which will be described in the section on Datatypes).

### 3.8 Garbage Collection

Dusk is a garbage-collected language which requires manual activation of the garbage collector. The keyword for doing this is:

```
gcCollect
```

Note that the garbage collector may only be called in special functions designated as "linear" (will only be executed once). The definition of a linear function is given in the next sub-section on Function Declarations. Details of why this is the case will be given in the section dedicated to Garbage Collection.

## 4 Functions and Declarations

### 4.1 Simple Functions

Functions are declared using the `fn` keyword, followed by an identifier for the function name, a list of the function arguments (and their types), and the return type (optional). If no return type is given, the function is said to have the return type `Unit`.

Ex:
```
fn f()
  if something() then return end
  waffle()
end

fn factorial(Int x) Int
  if x <= 0 then return 1
  else return x * factorial(x - 1) end
end
```

### 4.2 Main/Linear Function(s)

Instead of the `fn` keyword, functions may also be declared using the `lin` keyword, indicating that the function is a "linear" function.

Ex:
```
lin main()
  print("Hello World!")
end
```

Linear functions are guaranteed to only execute once. This means that they may only be called inside other linear functions, and never inside of a loop.

Programs require an initial `main` function as the first function to be executed. As implied by the example, `main` must be a linear function.

`TODO:` Linear function analysis.
`TODO:` Enforce linear main function.

### 4.3 Function Overloading

Functions may be given the same name as long as their first arguments are different* types.
 
**Some types that are different will be treated the same for the purposes of overloading, ex: arrays. More on this in the section on Datatypes (Overload Names).*

For example:
```
fn add(BigInt x, BigInt y) BigInt
  ...
end

fn add(Matrix m1, Matrix m2) Matrix
  ...
end
```

May both be declared and used in the same module without ambiguity, with the type system deciding at compile-time which one to use.

This functionality allows for builtin operators to be overloaded using their "explicit name", which we have actually already done in this example (overloading the `+` operator). Continuing from the following example, this would be a valid use of these overloads.

```
fn sum(Matrix a, Matrix b, Matrix c) Matrix
  return a + b + c + a
end
```

The following table describes how the overload name of a type is given:

| Type | Overload Name | Example |
|:-----|:--------------|:--------|
| Primitives | Taken verbatim | `Int`, `Float` => `Int`, `Float` |
| Pair  | `pair` | `(String, Bool)` => `pair`  |
| Triple | `triple` | `(Int, Int, Int)` => `triple` |
| N-uple | `t` + arity | `(Int, Float, Float, Float)` => `t4` |
| Arrays | Array dimension | `1d[Int]`, `3d[Float]` => `1d`, `3d` |
| Enums/Structs/Unions | Taken verbatim | - |
| Nullables | Ignore nullable | `String?`, `1d[Int]?` => `String`, `1d` |

The main implication is that types without explicit names (tuples, arrays, nullables) can only be overloaded to a limited extent.

### 4.4 Constant Declarations

### 4.5 Global Variables

Dusk supports the use of global variables, 

## 5. Module System

## 6. Sulfur Runtime


