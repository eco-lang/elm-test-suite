# What is Elm exactly?

Elm is a programming language created and maintained by Evan Czaplicki. Elm Exactly presents a precise 
specification of that language, but with an important distinction: its author is not the language’s designer.

This is an independent project, and I have no authority to define what Elm is or to standardise its design. 
That is why the specification’s title, *A Standard Definition of Elm?*, is a question. It asks: could this 
be an acceptable definition of Elm?

The specification takes Elm 0.19.x as its starting point, but deliberately departs from existing behaviour 
in some places. It proposes fixes for behaviour I consider buggy, resolves ambiguities, and makes choices 
intended to support consistent behaviour across implementations. These are proposals, with reasoning behind 
them, for readers to examine and challenge.

Elm Exactly has two parts: the proposed specification, and a suite of Elm programs run under several compilers 
to explore their behaviour and check agreement with the specification.

## Modelled on The Definition of Standard ML

The book follows The Definition of Standard ML (Revised), by Robin Milner, Mads Tofte, Robert Harper and 
David MacQueen (MIT Press, 1997). That book is the archetype for this one, which uses the same style, 
techniques and structure: a grammar, inference rules for the static and dynamic semantics, derived forms, 
and an initial basis.

Elm shares much with Standard ML, but leaves out many of its features: exceptions, user-defined operators, 
references, the module language of signatures and functors, and more. It adds row polymorphism, which types 
extensible records. It has a simpler syntax, and it aims to have no runtime exceptions.

## Bug or feature?

I am writing a new compiler for Elm, based on the existing implementations. Working from implementations 
that target JavaScript raises questions about which behaviours belong to Elm and which reflect quirks of 
that platform. Sometimes I look at how Elm handles something and have to ask myself: is this a bug or a feature?

That matters when implementing the language on another platform. Which behaviours should a new compiler 
preserve, and which could reasonably be corrected? A precise specification makes those choices explicit.

## What is the correct way to implement Elm?

I draw on three main sources for guidance: ML and the Hindley–Milner type system; IEEE 754 for floating-point 
arithmetic; and Unicode for text. Where Elm’s behaviour is ambiguous, I have leaned towards those foundations, 
while considering efficient implementation and the aim of avoiding runtime exceptions.

That aim requires decisions about operations for which mathematics provides no result. In this specification, 
for example, modBy 0 x is defined to return 0. This is an engineering choice that gives the operation a result 
where it would otherwise be undefined.

Elm Exactly seeks to answer the question: what would a correct alternative implementation of Elm look like? 
It explores that question by specifying the language’s behaviour precisely, checking implementations against 
that specification, and making explainable engineering decisions wherever a compromise is needed.

<actions>
<button-link href="/standard" text="OK, Got It! →"></button-link>
</actions>
