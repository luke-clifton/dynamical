# Dynamical

`Dynamical` is a Haskell library for numerically solving dynamical systems.

This library is still very young. API is guaranteed to change.

Systems are described at a high level using a Functional Reactive
Programming (FRP) style, and can be solved using a number of integration
techniques. The library is designed for simulation only, so all computation
is pure, that is, we can not get events from the outside world. This allows
us to implement some advanced integration and time stepping techniques that
would otherwise not be possible.

