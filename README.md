# Bestowed Objects and Atomic Message Passing

This repository contains mechanized formalizations of variations
of an actor calculus using bestowed objects and atomic message
passing, accompanying the
paper
[Actors Without Borders: Amnesty for Imprisoned State](https://arxiv.org/abs/1704.03094) [PLACES'17].

The repository is organized as follows:

- [vanilla](vanilla) contains the mechanization of the calculus
  presented in the original Actors Without Borders paper. Any
  passive object can be bestowed, and the owner of a bestowed
  object is fixed for life (and is always the creator of the
  object).
- [transfer](transfer) contains a variation of the calculus where
  objects can be created as "transferable". These objects behave
  as bestowed objects, but the runtime can transfer ownership of
  such an object between actors.
- [private](private) contains a variation where atomic message
  passing is handled using private message queues, rather than
  just batching messages. This allows an actor to react to
  intermediate responses from another actor without losing
  atomicity.