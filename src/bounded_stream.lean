import verification.verify
import compile_fast2

variables {σ α ι γ β : Type}
variables (R : Type) [add_zero_class R] [has_one R] [has_mul R]

structure BoundedStream (σ ι α : Type) :=
(next    : σ → σ)
(current : σ → ι)
(value   : σ → α)
(ready   : σ → bool)
(valid   : σ → bool)
(bound   : ℕ)
(state   : σ)

namespace BoundedStream

instance : bifunctor (BoundedStream σ) :=
{ bimap := λ _ _ _ _ i v g, { g with value := v ∘ g.value, current := i ∘ g.current } }

def mul {σ'} [has_hmul α β γ] (a : BoundedStream σ ι α) (b : BoundedStream σ' ι β) : BoundedStream (σ × σ') ι γ := sorry

def range (n : ℕ) : BoundedStream ℕ ℕ ℕ :=
{ next := λ k, k+1,
  current := id,
  value := id,
  ready := λ _, tt,
  valid := λ k, k < n,
  bound := n,
  state := 0,
}

#check range <$> range 3

end BoundedStream

def context := Ident → IdentVal R

variables {R}
def BoundedStreamGen.of_gen {ι' α'} [StreamEval R ι ι'] [StreamEval R α α']
: BoundedStreamGen R ι α → BoundedStream (context R) ι' α' := λ g',
let g : BoundedStreamGen R (context R → ι') (context R → α') :=
    bimap StreamEval.eval StreamEval.eval g' in
{ current := g.current,
  value   := g.value,
  ready   := λ c, 0 < (g.ready.eval c).to_nat,
  valid   := λ c, 0 < (g.valid.eval c).to_nat,
  next    := g.next.eval,
  -- are these two sufficiently general? requires that behavior not depend on state outside of initialize
  state   := g.initialize.eval default,
  bound   := g.bound $ g.initialize.eval default
}
