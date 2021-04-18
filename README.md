# TLA+ Cookbook

> A collection of various [TLA+](https://lamport.azurewebsites.net/tla/tla.html) examples and helper functions for learning.

[![License](http://img.shields.io/badge/license-MIT-blue.svg)](https://raw.githubusercontent.com/miguelmota/tla-cookbook/master/LICENSE)
[![PRs Welcome](https://img.shields.io/badge/PRs-welcome-brightgreen.svg)](#contributing)

## Examples

### Random Integer

```tla
EXTENDS Integers

RandomElement(1..100)
```

Result:

```
56
```

[RandomIntegers.tla](./examples/RandomIntegers.tla)

### Set

```
{1,2,3,3,4}
```

Result:

```
{1,2,3,4}
```

### Largest number is Set

Returns the largest element in set.

```
EXTENDS Integers

Maximum(S) == IF S = {} THEN -1 ELSE CHOOSE x \in S: \A y \in S: y <= x

Maximum({4,7,5})
```

Result:

```
7
```

[SetLargestNumber.tla](./examples/SetLargestNumber.tla)

### Smallest number is Set

Returns the smallest element in set.

```
EXTENDS Integers

Maximum(S) == IF S = {} THEN -1 ELSE CHOOSE x \in S: \A y \in S: y <= x

Maximum({4,7,5})
```

Result:

```
4
```

[SetSmallestNumber.tla](./examples/SetSmallestNumber.tla)

## Set difference

```
EXTENDS Integers
VARIABLE S, T, X

S = (10..20)
T = (1..14)
X' = S \ T
```

```
{15, 16, 17, 18, 19, 20}
```

[SetDifference.tla](./examples/SetDifference.tla)

## Set common

Asserts that any two elements of T have an element in common.

```
T = {{1,2}, {1,3}, {2,3}}

\A X, Y \in T : X \cap Y # {}
```

Result:

```
TRUE
```

[SetCommon.tla](./examples/SetCommon.tla)

### Sequences

```
<<1, 2, 3>>
```

### Append To Sequence

```tla
EXTENDS Sequences
VARIABLE S

S = <<1>>
S' = S \o <<2>>
```

Result:

```
<<1, 2>>
```

[SequenceAppend.tla](./examples/SequenceAppend.tla)

### Sum Sequence

```tla
EXTENDS Integers, Sequences

SumSeq(S) ==
  LET seq == S
    Sum[i \in 1..Len(seq)] == IF i = 1 THEN seq[i] ELSE seq[i] + Sum[i-1]
  IN IF seq = <<>> THEN 0 ELSE Sum[Len(seq)]

SumSeq(<<1, 2, 3>>)
```

Result:

```
6
```

[SumSequence.tla](./examples/SumSequence.tla)

## Contributing

Pull requests are welcome!

For contributions please create a new branch and submit a pull request for review.

## License

[MIT](LICENSE)
