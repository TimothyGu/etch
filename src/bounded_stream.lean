import verification.verify
import tactic

class has_hmul (α β : Type*) (γ : out_param Type*) :=
  (mul : α → β → γ)
instance hmul_of_mul {α : Type*} [has_mul α] : has_hmul α α α := ⟨has_mul.mul⟩
infix ` ⋆ `:71 := has_hmul.mul

variables {σ α ι γ β : Type}
variables (R : Type) [add_zero_class R] [has_one R] [has_mul R]
def context := Ident → IdentVal R
variables [linear_order ι] [has_hmul α β γ]
[semiring α]
[semiring β]
[semiring γ]

noncomputable instance finsupp.has_mul : has_mul (ι →₀ β) := ⟨λ a b, finsupp.zip_with (*) (zero_mul _) a b⟩
noncomputable instance finsupp.mul_zero_class : mul_zero_class (ι →₀ α) :=
{ zero_mul := sorry, mul_zero := sorry, .. finsupp.has_mul, .. finsupp.has_zero }

noncomputable instance finsupp.distrib : distrib (ι →₀ α) :=
{ left_distrib := sorry, right_distrib := sorry, ..finsupp.has_add, ..finsupp.mul_zero_class }

#check non_unital_semiring

-- todo
-- noncomputable instance finsupp.nus : non_unital_semiring (ι →₀ α) :=
-- { .. finsupp.has_add, .. finsupp.mul_zero_class}

structure status (σ ι α : Type) :=
(next  : σ)
(index : ι)
(value : α)
(ready : bool)
(valid : bool)
(state : σ) -- redundant

structure BoundedStream (σ ι α : Type) :=
(next  : function.End σ)
(index : σ → ι)
(value : σ → α)
(ready : σ → bool)
(valid : σ → bool)
(bound : ℕ)
(state : σ)
(bound_valid : ∀ i, bound ≤ i → ready (next ^ i • state) = ff ∧ valid (next ^ i • state) = ff)

variables {R}
def BoundedStreamGen.of_gen {ι' α'} [StreamEval R ι ι'] [StreamEval R α α']
: BoundedStreamGen R ι α → BoundedStream (context R) ι' α' := λ g',
let g : BoundedStreamGen R (context R → ι') (context R → α') :=
    bimap StreamEval.eval StreamEval.eval g' in
{ index := g.current,
  value := g.value,
  ready := λ c, 0 < (g.ready.eval c).to_nat,
  valid := λ c, 0 < (g.valid.eval c).to_nat,
  next  := g.next.eval,
  -- are these two sufficiently general? requires that behavior not depend on state outside of initialize
  state := g.initialize.eval default,
  bound := g.bound $ g.initialize.eval default,
  bound_valid := sorry,
}

namespace BoundedStream

variables (s : BoundedStream σ ι α)

def now : status σ ι α :=
{ next  := s.next s.state,
  index := s.index s.state,
  value := s.value s.state,
  ready := s.ready s.state,
  valid := s.valid s.state,
  state := s.state }

--[add_zero_class α] [has_one α] [has_mul α]

instance : bifunctor (BoundedStream σ) :=
{ bimap := λ _ _ _ _ i v g, { g with value := v ∘ g.value, index := i ∘ g.index } }

def range (n : ℕ) : BoundedStream ℕ ℕ ℕ :=
{ next  := λ k, k+1,
  index := id,
  value := id,
  ready := λ _, tt,
  valid := λ k, k < n,
  bound := n,
  state := 0,
  bound_valid := sorry,
}
example : BoundedStream ℕ ℕ (BoundedStream ℕ ℕ ℕ) :=  range <$> range 3

def δ : BoundedStream σ ι α :=
{ s with state := s.next s.state, bound := s.bound.pred, bound_valid :=
  begin
    have bv := s.bound_valid,
    intros _ ih,
    cases em (s.bound = 0),
    {
      simp only [h, nat.pred_zero] at ih,
      rw ←h at ih,
      have := bv (i+1) (le_add_right ih),
      change s.ready (s.next ^ i • s.next • s.state) = ff ∧ s.valid (s.next ^ i • s.next • s.state) = ff,
      rw ← mul_smul,
      rw ← pow_succ',
      exact this,
    },
    {
      change s.ready (s.next ^ i • s.next • s.state) = ff ∧ s.valid (s.next ^ i • s.next • s.state) = ff,
      obtain ⟨_, this⟩ := nat.exists_eq_succ_of_ne_zero h,
      simp [this, nat.pred] at ih,
      have ih' : w.succ ≤ i.succ := nat.succ_le_succ ih,
      rw ← this at ih',
      have := bv i.succ ih',
      rw ← mul_smul,
      rw ← pow_succ',
      exact this,
    }
  end
}

def stream_elim (P : BoundedStream σ ι α → Prop) : (∀ (s : BoundedStream σ ι α), s.bound = 0 → P s) → (∀ (s : BoundedStream σ ι α), P s.δ → P s) → ∀ s, P s := begin
intros base h s,
generalize h : s.bound = bound,
induction bound generalizing s,
{ apply base, rw h_1 },
{ apply h, apply bound_ih, simp [δ, *] },
end

noncomputable def  eval₀ {σ ι α} [has_zero α] (s : BoundedStream σ ι α) : ι →₀ α :=
if s.ready s.state then finsupp.single (s.index s.state) (s.value s.state) else 0

noncomputable def eval' : ℕ → (BoundedStream σ ι α) → ι →₀ α
| 0 _ := 0
| (n+1) s := eval₀ s + eval' n s.δ

noncomputable def eval : ι →₀ α  := eval' s.bound s

@[simp] lemma one_app {α} {x} : (1 : function.End α) x = x := rfl .

@[simp] lemma eval_bound_zero : s.bound = 0 → eval₀ s = 0 := begin
intros h,
simp only [eval₀],
split_ifs with ready,
{
  apply false.rec,
  obtain ⟨ nr, _ ⟩:= s.bound_valid 0 (nonpos_iff_eq_zero.mpr h),
  { simp at nr,
    convert ready,
    simp [nr] } },
{ refl }
end

@[simp] lemma bound_delta_zero : s.bound = 0 → s.δ.bound = 0 :=
by simp [δ, nat.pred] { contextual := tt }
@[simp] lemma bound_delta_succ {n : ℕ} : s.bound = n.succ → s.δ.bound = n :=
by simp [δ, nat.pred] { contextual := tt }

lemma eval_identity : eval s = eval₀ s + eval s.δ := begin
simp [eval, eval'],
cases em (s.bound = 0),
{ simp [h, eval'], },
{ obtain ⟨_, this⟩ := nat.exists_eq_succ_of_ne_zero h,
  rw [this, eval', bound_delta_succ],
  assumption }
end

variables {σ₁ σ₂ : Type}
(a : BoundedStream σ₁ ι α) (b : BoundedStream σ₂ ι β)
(s₁ : σ₁) (s₂ : σ₂)

def state_le {α β : Type} (a : BoundedStream σ₁ ι α) (b : BoundedStream σ₂ ι β)
: σ₁ × σ₂ → bool :=
λ s, a.index s.1 < b.index s.2 ∨ (a.index s.1 = b.index s.2 ∧ a.ready s.1 ≤ b.ready s.2)

def state_lt {α β : Type} (a : BoundedStream σ₁ ι α) (b : BoundedStream σ₂ ι β)
: σ₁ × σ₂ → Prop :=
λ s, a.index s.1 < b.index s.2 ∨ (a.index s.1 = b.index s.2 ∧ a.ready s.1 < b.ready s.2)

instance : preorder (BoundedStream σ ι α) :=
{le := λ a b, state_le a b (a.state, b.state),
 le_refl := by simp [state_le],
 le_trans := begin simp [state_le], intros _ _ _ h1 h2, cases h1; cases h2, apply or.inl, apply lt_trans h1 h2, apply or.inl, rw ← h2.1, assumption, apply or.inl, rw h1.1, assumption, apply or.inr, split, exact eq.trans h1.1 h2.1, apply le_trans h1.2 h2.2, end
}

#check acc
class Merge (σ : Type) := (merge : σ × σ → σ)

def hmul {α β γ} [has_hmul α β γ]
(a : BoundedStream σ₁ ι α) (b : BoundedStream σ₂ ι β) : BoundedStream (σ₁ × σ₂) ι γ :=
{ next  := λ s, if state_le a b s then (a.next s.1, s.2) else (s.1, b.next s.2),
  index := λ s, max (a.index s.1) (b.index s.2),
  value := λ s, (a.value s.1) ⋆ (b.value s.2),
  ready := λ s, a.ready s.1 && b.ready s.2 && (a.index s.1 = b.index s.2),
  valid := λ s, a.valid s.1 && b.valid s.2,
  bound := a.bound + b.bound,
  state := (a.state, b.state),
  bound_valid := begin sorry end,
}

-- def mul {α} [has_mul α] [Merge σ]
-- (a b : BoundedStream σ ι α) : BoundedStream σ ι γ :=
-- { next  := λ s, if state_le a b s then (a.next s.1, s.2) else (s.1, b.next s.2),
--   index := λ s, max (a.index s.1) (b.index s.2),
--   value := λ s, (a.value s.1) ⋆ (b.value s.2),
--   ready := λ s, a.ready s.1 && b.ready s.2 && (a.index s.1 = b.index s.2),
--   valid := λ s, a.valid s.1 && b.valid s.2,
--   bound := a.bound + b.bound,
--   state := (a.state, b.state),
--   bound_valid := begin sorry end,
-- }

instance {α β γ} [has_hmul α β γ] : has_hmul (BoundedStream σ₁ ι α) (BoundedStream σ₂ ι β) (BoundedStream (σ₁ × σ₂) ι γ) := ⟨hmul⟩

@[simp] lemma mul_eval₀
(a : BoundedStream σ₁ ι α) (b : BoundedStream σ₂ ι α)
: (a ⋆ b : BoundedStream _ _ α).eval₀ = a.eval₀ * b.eval₀ := begin
simp [hmul, eval₀],
split_ifs with h h1 h2; try {simp [not_and_distrib] at h |- }; try { simp }; sorry
-- automate more ^
end

lemma mul_next_state : (a ⋆ b : BoundedStream _ _ γ).next (s₁, s₂) = (a.next s₁, s₂) ∨
                       (a ⋆ b : BoundedStream _ _ γ).next (s₁, s₂) = (s₁, b.next s₂) :=
begin
  simp only [(⋆), BoundedStream.hmul],
  cases a.state_le b (s₁, s₂); simp [prod.fst],
end

lemma mul_succ : (a ⋆ b : BoundedStream _ _ γ).δ = a.δ ⋆ b ∨
                 (a ⋆ b : BoundedStream _ _ γ).δ = a ⋆ b.δ :=
begin
sorry,
end
end BoundedStream

-- structure SimpleStream (σ ι α : Type) [linear_order ι] extends BoundedStream σ ι α :=
-- (monotonic : ∀ s, index s ≤ index (next s))
-- (reduced : ∀ s t, ready s → ready t → index s = index t → s = t)

class is_simple (q : BoundedStream σ ι α) : Prop :=
(monotonic : ∀ s, q.index s ≤ q.index (q.next s))
(reduced : ∀ s t, q.ready s → q.ready t → q.index s = q.index t → s = t)

variables {σ₁ σ₂ : Type}

instance hmul.is_simple
(a : BoundedStream σ₁ ι α) (b : BoundedStream σ₂ ι β)
[is_simple a] [is_simple b] : is_simple (a ⋆ b : BoundedStream _ _ γ) :=
⟨begin rintros ⟨s₁, s₂⟩,
    cases BoundedStream.mul_next_state a b s₁ s₂;
    { rw h, apply max_le_max; simp only [(⋆), BoundedStream.hmul, BoundedStream.index, is_simple.monotonic] },
  end, begin
    rintro ⟨s₁, s₂⟩ ⟨t₁, t₂⟩ aready bready ih,
    -- ready → ai₁ = bi₁, ai₂ = bi₂. index = index → ai₁ = ai₂. reduced a → s₁ = s₂, etc
    sorry
    end⟩

--variables
--(a : SimpleStream σ₁ ι α) (b : SimpleStream σ₂ ι α)

--noncomputable instance : has_hmul (ι →₀ α) (ι →₀ β) (ι →₀ γ) := ⟨finsupp.zip_with (⋆) $ hmul_zero_class.mul_zero 0⟩
--set_option trace.class_instances true
open BoundedStream
lemma multiply : ∀ (a b c d : ι →₀ α), (a + b) * (c + d) = a*c + a*d + b*c + b*d := begin
intros,
rw [left_distrib],
rw [right_distrib],
rw [right_distrib],
abel,
end

variables
(a : BoundedStream σ ι α) (b : BoundedStream σ ι α)
[is_simple a] [is_simple b]

lemma lt_mul_is_zero  : a < b → a.eval₀ * b.eval = 0 := sorry
lemma lt_mul_0_is_zero  : a < b → a.eval₀ * b.eval₀ = 0 := sorry
lemma le_succ_is_left  : a ≤ b → (a ⋆ b : BoundedStream _ _ α).δ = a.δ ⋆ b := sorry
--lemma lt_mul_is_zero' : ¬ state_lt a b (a.state, b.state) → b.eval₀ * a.eval = 0 := sorry
--lemma mono_delta [is_simple a] : a.now.index ≤ a.δ.now.index := sorry
lemma mono_delta [is_simple a] : a ≤ a.δ := sorry
instance [is_simple a] : is_simple a.δ := sorry

example {α} [preorder α] : ∀ a b c : α, a < b → b ≤ c → a < c := begin library_search, end
theorem mul_spec
: (a ⋆ b : BoundedStream _ _ α).eval = a.eval * b.eval := begin
cases em (a < b),
rw [a.eval_identity, (a ⋆ b : BoundedStream _ _ α).eval_identity],
rw [right_distrib],
rw [lt_mul_is_zero _ _ h],
rw mul_eval₀ a b,
rw [lt_mul_0_is_zero],
rw le_succ_is_left,
simp only [zero_add],
-- induction ^

-- rw [a.eval_identity, b.eval_identity, (a ⋆ b : BoundedStream _ _ α).eval_identity],
-- rw mul_eval₀ a b,
-- rw [lt_mul_is_zero _ _ (lt_of_lt_of_le h (mono_delta _))],
-- rw multiply,
--cases em (state_lt a b (a.state, b.state)),
--cases mul_succ a b,

end

. /-
for mul_eval₀:
  not ready -> eval₀ = 0

a < b → a.eval₀ * b.eval = 0
merge valid-bound/ready?
-/ .
