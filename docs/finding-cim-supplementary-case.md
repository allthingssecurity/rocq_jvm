# Finding: CaseInsensitiveMap treats keys that differ only in the case of a supplementary character as different keys

Found 2026-10-23 while writing the specification for the `CaseInsensitiveMap` proof (the spec "a map keyed by
`String.equalsIgnoreCase`" cannot hold). Not reported anywhere; reporting is the user's call.

## What happens
`CaseInsensitiveMap` (camel-util, the headers map) buckets keys by `caseInsensitiveHash`, which folds each UTF-16
**char** separately (`Character.toLowerCase(Character.toUpperCase(c))`), but compares keys with
`String.equalsIgnoreCase`, which since JDK 16 (JDK-8248655) folds **code points**. For a supplementary-plane letter
the two halves of the surrogate pair are folded separately, which does nothing, so two keys that are equal
ignoring case get different hashes and usually land in different buckets.

Reproduced with the real classes (javac 21.0.12 --release 17, `rocq-jvm/classes/cim-main`, `cim-fix`):

```
key U+10400 (DESERET CAPITAL LETTER LONG I) vs U+10428 (DESERET SMALL LETTER LONG I)
                           equalsIgnoreCase  get(lower)  containsKey(lower)  size after put(upper), put(lower)
main 36bebb520a63           true              null        false               2
fix  27aeb4f860d9           true              null        false               2
```

So the map stores both keys, and a lookup in the other case misses, contrary to the class contract ("uses case
insensitive keys"). Affected scripts: Deseret, Osage, Old Hungarian, Warang Citi, Medefaidrin, Adlam, Vithkuqi
and others with supplementary case pairs.

## Severity
Minor. HTTP/JMS header names are ASCII in practice; a header name with such letters is very unusual. It is,
however, a behaviour change versus the earlier `TreeMap(String.CASE_INSENSITIVE_ORDER)`-based map, whose comparator
also folds code points (JDK 16+), so those keys were equal there. To be checked before any report: when the custom
hash table replaced the TreeMap, and a JIRA duplicate search.

## Fix options
- Fold code points in `caseInsensitiveHash` (iterate with `codePointAt`, fold with
  `Character.toLowerCase(Character.toUpperCase(cp))`, hash the folded code point's chars), or
- keep the char loop but fold surrogate pairs as code points.
Either way the hash must be a function of the equalsIgnoreCase class of the key. That is exactly the
lemma the Rocq proof needs ("equalsIgnoreCase a b -> hash a = hash b"), so the proof will check the fix.

## Consequence for the proof plan
The ordered-map spec is stated with key equality = the per-char fold that the code actually uses, and a separate
theorem relates it to `equalsIgnoreCase`: equal for strings without supplementary case pairs, different in general
(this counterexample).
