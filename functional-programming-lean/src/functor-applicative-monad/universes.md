# Universes

In the interests of simplicity, this book has thus far papered over an important feature of Lean: _universes_.
A universe is a type that classifies other types.
Two of them are familiar: `Type` and `Prop`.
`Type` classifies what are referred to as "small types": types that do not themselves contain any types.
`Prop` classifies propositions that may be true or false.

For technical reasons, more universes than these two are needed.
In particular, `Type` cannot itself be a `Type`.
This would allow a logical paradox to be constructed and undermine Lean's usefulness as a theorem prover.
