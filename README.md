# antifunext without antifunext

As a small exercise,
I took András Kovács' [antifunext](https://github.com/AndrasKovacs/antifunext)
and removed all the interesting stuff related to refuting function extensionality.
The result is an Agda formalization of
a simple model of Martin-Löf type theory
(with pi, sigma, nat, identity, universes).

Note:
the Agda code does not contain a definition of "model of type theory".
It is not machine-checked that the code actually constitutes a model
(and I might have made mistakes while deleting stuff).
