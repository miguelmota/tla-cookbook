# TLA+ Cookbook

> A collection of various [TLA+](https://lamport.azurewebsites.net/tla/tla.html) examples and helper functions for learning.

[![Language](https://shields.io/badge/language-TLA+-violet?style=flat)](https://lamport.azurewebsites.net/tla/tla.html)
[![License](http://img.shields.io/badge/license-MIT-blue.svg)](https://raw.githubusercontent.com/miguelmota/tla-cookbook/master/LICENSE)
[![PRs Welcome](https://img.shields.io/badge/PRs-welcome-brightgreen.svg)](#contributing)

## Examples

### Print

Use _Print_ operator defined in standard module _TLC_.

```tla
EXTENDS TLC

/\ Print(<<"Hello world">>, TRUE)
```

Result:

```tla
<<"Hello world">>
```

[Print.tla](./examples/Print.tla)

### Set

Create a set.

```tla
/\ {1, 2, 3, 3, 4}
```

Result:

```tla
{1, 2, 3, 4}
```

### Range Set

_N..M_ is set of all numbers between _N_ and _M_.

```tla
EXTENDS Integers

/\ 1..5
```

Result:

```tla
1..5
```

[RangeSet.tla](./examples/RangeSet.tla)

### Set Contains

Check if set _S_ contains value _x_ with _x \in S_.

```tla
EXTENDS Integers

/\ 2 \in {1, 2, 3}
/\ 4 \in 1..3
```

Result:

```tla
TRUE
FALSE
```

[SetContains.tla](./examples/SetContains.tla)

### Filter set

`{v \in S : P}` is the subset of _S_ consising of all _v_ satisfying _P_. _P_ must resolve to a boolean.

```tla
EXTENDS Integers

/\ S = {1, 2, 3, 4, 5}
/\ {v \in S : v > 3}
```

Result:

```tla
{4, 5}
```

[FilterSet.tla](./examples/FilterSet.tla)

### Map set

`{e : v \in S}` is the set of all `e` for `v` in `S`. The function `e` is applied to every element in set.

```tla
EXTENDS Integers

/\ S = {1, 2, 3, 4, 5}
/\ {v^2: v \in S}
```

Result:

```tla
{1, 4, 9, 16, 25}
```

[MapSet.tla](./examples/MapSet.tla)

### Largest number is Set

Get the largest element in set.

```tla
EXTENDS Integers

Maximum(S) == IF S = {} THEN -1 ELSE CHOOSE x \in S: \A y \in S: y <= x

/\ Maximum({4, 7, 5})
```

Result:

```tla
7
```

[SetLargestNumber.tla](./examples/SetLargestNumber.tla)

### Smallest number is Set

Get the smallest element in set.

```tla
EXTENDS Integers

Maximum(S) == IF S = {} THEN -1 ELSE CHOOSE x \in S: \A y \in S: y <= x

/\ Maximum({4, 7, 5})
```

Result:

```tla
4
```

[SetSmallestNumber.tla](./examples/SetSmallestNumber.tla)

## Set difference

Get the difference of two sets.

```tla
EXTENDS Integers
VARIABLE S, T

/\ S = (10..20)
/\ T = (1..14)
/\ S \ T
```

```tla
{15, 16, 17, 18, 19, 20}
```

[SetDifference.tla](./examples/SetDifference.tla)

## Set common

Asserts that any two elements of T have an element in common.

```tla
VARIABLE T

/\ T = {{1, 2}, {1, 3}, {2, 3}}
/\ R = {{1, 1}, {1, 3}, {2, 3}}

/\ \A X, Y \in T : X \cap Y # {}
/\ \A X, Y \in R : X \cap Y # {}
```

Result:

```tla
TRUE
FALSE
```

[SetCommon.tla](./examples/SetCommon.tla)

### Sequences

Create a sequence.

```tla
/\ <<1, 2, 3>>
```

### Append To Sequence

Append to a sequence.

```tla
EXTENDS Sequences
VARIABLE S

/\ S = <<1>>
/\ S \o <<2>>
```

Result:

```tla
<<1, 2>>
```

[SequenceAppend.tla](./examples/SequenceAppend.tla)

### Sum Sequence

Sum all values of a sequence.

```tla
EXTENDS Integers, Sequences

SumSeq(S) ==
  LET seq == S
    Sum[i \in 1..Len(seq)] == IF i = 1 THEN seq[i] ELSE seq[i] + Sum[i-1]
  IN IF seq = <<>> THEN 0 ELSE Sum[Len(seq)]

/\ SumSeq(<<1, 2, 3>>)
```

Result:

```tla
6
```

[SumSequence.tla](./examples/SumSequence.tla)

### Local variables

Add local definitions to an expression.

```tla
EXTENDS Integers

/\ LET x == 1
       y == 2
       z == 3
   IN <<x + y + z>>
```

Result:

```tla
6
```

[LocalVariables.tla](./examples/LocalVariables.tla)

### Is even

True is value is even.

```tla
EXTENDS Integers

IsEven(x) == x % 2 = 0

/\ IsEven(2)
```

Result:

```tla
TRUE
```

[IsEven.tla](./examples/IsEven.tla)

### Is odd

True is value is odd.

```tla
EXTENDS Integers

IsOdd(x) == x % 2 = 1

/\ IsOdd(2)
```

Result:

```tla
TRUE
```

[IsOdd.tla](./examples/IsOdd.tla)

### Random Integer

Get a random integer within a range.

```tla
EXTENDS Integers

/\ RandomElement(1..100)
```

Result:

```tla
56
```

[RandomIntegers.tla](./examples/RandomIntegers.tla)

## Contributing

Pull requests are welcome!

For contributions please create a new branch and submit a pull request for review.

## License

[MIT](LICENSE)
