# SM-Proc

A well-typed symmetric-monoidal category of concurrent processes in [Idris](http://www.idris-lang.org/).

Still very experimental. [Run the example](https://github.com/jameshaydon/smproc#how-to-run-the-example).

## Idea

This library helps in defining a system of concurrent communicating processes. The processes are structured as morphisms in a symettric monoidal category; see the [nLab](https://ncatlab.org/nlab/show/symmetric+monoidal+category) for an explanation of what those are.

* The objects are vectors of *oriented typed wires*, which are types decorated with one of the orientations: `Up` or `Down`. The monoidal structure on the objects is simply vector concatenation: `++`.

* The morphisms `[u_0, ..., u_m] -> [w_0, ..., w_n]` in the category are represented by concurrent process which have `u_0`, ..., `u_m` as *top* wires and `w_0`, ..., `w_n` as *bottom* wires. On both the top and bottom a process may have input and output wires, because of the orientation of those wires. The type of processes is given by the dependent type

       Hom [u_0, ..., u_m] [w_0, ..., w_n].

* Processes `f : Hom as bs` and `g : Hom bs cs` may be composed, producing `f -*- g : Hom as cs`, and this makes a category. This is acheived by joining the appropriate communication channels between `f` and `g`.

* There is also a monoidal structure producing

       f + g : Hom (as ++ as') (bs ++ bs')

whenever

      f : Hom as  bs
      g : Hom as' bs'

This runs the processes `f` and `g` in parallel. This makes the category of processes a symetric monoidal category, because also have a special process:

      sym: Hom (as ++ bs) (bs ++ as)

Because we get a symetric monoidal category, we reason about the processes using [string diagrams](https://ncatlab.org/nlab/show/string+diagram).

## Example

The library defines some helper functions for defining processes. One is:

    mkPure: (name: String) -> (f: a -> b) -> Hom [Down a] [Down b]

Given a pure function `f: a -> b`, this produces a process

      │
      ↓  a   <-- downwards input wire of type a
      │
    ┌─┴─┐
    │ f │
    └─┬─┘
      │
      ↓  b   <-- downwards input wire of type a
      │

There is also `upPrinter` and `downPrinter`:

        │          ┌───────┐
        ↓  a       │ print │
        │          └───┬───┘
    ┌───┴───┐          │
    │ print │          ↑  a
    └───────┘          │

    downPrinter    upPrinter

Note that one can be obtained from the other using the `dualise` function:

    dualise: Mor as bs -> Mor (dual bs) (dual as)

where the dual of a typed wire is the same wire going in the other direction.

We also have `cap` and `cup` which are the *unit* and *co-unit* respectively:

     ↓    ↑
     │    │
     └────┘

    cup : Mor [Down a, Up a] []

     ┌────┐
     │    │
     ↓    ↑

    cap : Mor [Down a, Up a] []

With these we can already produce a non-trivial composite process (See `Examples.idr`):

    myProc: Mor [Down Int] []
    myProc =     downIntWire + cap
             -*- (splice -*- inc -*- gt5) + upIntWire
             -*- downPrinter + cup

where:

    gt5: Mor [Down Int] [Down Int, Down Int]
    gt5 = mkPure "gt5: " (\n => if n > 5 then Left n else Right n) -.- splitEither

    inc: Mor [Down Int] [Down Int]
    inc = mkPure "inc: " (\i => i + 1)

    downIntWire: Mor [Down Int] [Down Int]
    downIntWire = mkPure "down int: " id

    upIntWire: Mor [Up Int] [Up Int]
    upIntWire = dualise downIntWire

This can be visualised as:

       ↓
       │   ┌─────┐
       └───┤     │
           │     │
           ↓     ↑
           │     │
        ┌──┴──┐  │
        │  +1 │  │
        └──┬──┘  │
           │     │
           ↓     │
           │     │
        ┌──┴──┐  │
        │ > 5 │  │
        └─┬─┬─┘  │
        ┌─┘ ↓    ↑
        │   │    │
        ↓   └────┘   
        │    
    ┌───┴───┐
    │ print │
    └───────┘

Which is a process that, when an integer is sent to it's only input wire, will keep incrementing that integer untill it is greater than 6, and this it will print it.

## How to run the example

* Install Idris: [instructions](https://github.com/idris-lang/Idris-dev/wiki/Installation-Instructions).
* Download the repo: `git clone https://github.com/jameshaydon/smproc.git`
* Start the idris repl: `$ idris Examples.idr` (compilation will take a while)
* Run main: `:exec main`

## TODO

* Make the abstract representation (started in `Bord.idr`)
* Optimise the abstract representation using usual string diagram transformations
* Write the compiler: `abstract rep --> process`
* For the moment the topology is fixed at compile-time. Think about how this can be more flexible.
* Make a version for the javascript targer, maybe using [js-csp](https://github.com/ubolonton/js-csp)
