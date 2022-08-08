import verification.verify
import tactic

open_locale classical

class has_hmul (α β : Type*) (γ : out_param Type*) :=
  (mul : α → β → γ)
instance hmul_of_mul {α : Type*} [has_mul α] : has_hmul α α α := ⟨has_mul.mul⟩

variables {σ α ι γ β : Type}
variables (R : Type) [add_zero_class R] [has_one R] [has_mul R]

def context := Ident → IdentVal R

variables
[linear_order ι] [has_hmul α β γ]
[semiring α] [semiring β] [semiring γ]

noncomputable instance finsupp.has_mul  : has_mul (ι →₀ α) :=
⟨λ a b, finsupp.zip_with (*) (zero_mul _) a b⟩

lemma finsupp.mul_apply (g₁ g₂ : ι →₀ α) (a : ι) : (g₁ * g₂) a = g₁ a * g₂ a := rfl

#check pi.distrib -- todo, tactic like this?
noncomputable instance finsupp.non_unital_semiring : non_unital_semiring (ι →₀ α) :=
{
  zero := 0,
  add_assoc := λ a b c, fun_like.ext _ _ (by simp [finsupp.add_apply, add_assoc]),
  zero_add  := λ a,     fun_like.ext _ _ (by simp [finsupp.add_apply]),
  add_zero  := λ a,     fun_like.ext _ _ (by simp [finsupp.add_apply]),
  add_comm  := λ a b,   fun_like.ext _ _ (by simp [finsupp.add_apply, add_comm] ),
  zero_mul  := λ a,     fun_like.ext _ _ (by simp [finsupp.mul_apply]),
  mul_zero  := λ a,     fun_like.ext _ _ (by simp [finsupp.mul_apply]),

  left_distrib  := λ a b c, by simp [fun_like.ext_iff, finsupp.mul_apply, finsupp.add_apply, left_distrib],
  right_distrib := λ a b c, by simp [fun_like.ext_iff, finsupp.mul_apply, finsupp.add_apply, right_distrib],
  mul_assoc     := λ a b c, by simp [fun_like.ext_iff, finsupp.mul_apply, mul_assoc],

  ..finsupp.has_mul, ..finsupp.has_add, }

structure Stream (σ ι α : Type) :=
(next  : function.End σ)
(index : σ → ι)
(value : σ → α)
(ready : σ → Prop)
(valid : σ → bool)
(state : σ)

structure BoundedStream (σ ι α : Type) extends Stream σ ι α :=
(bound : ℕ)
(bound_valid : ∀ i, bound ≤ i → ready (next ^ i • state) = ff ∧ valid (next ^ i • state) = ff)

structure status (σ ι α : Type) :=
(next  : σ)
(index : ι)
(value : α)
(ready : Prop)
(valid : bool)
(state : σ)

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

def now {σ ι α} (s : BoundedStream σ ι α) : status σ ι α :=
{ next  := s.next s.state,
  index := s.index s.state,
  value := s.value s.state,
  ready := s.ready s.state,
  valid := s.valid s.state,
  state := s.state }

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

--@[elab_as_eliminator]
def stream_elim (P : BoundedStream σ ι α → Prop) :
(∀ (s : BoundedStream σ ι α), s.bound = 0 → P s) → (∀ (s : BoundedStream σ ι α), P s.δ → P s) → ∀ s, P s :=
begin
  intros base h s,
  generalize h : s.bound = bound,
  induction bound generalizing s,
  { apply base, rw h_1 },
  { apply h, apply bound_ih, simp [δ, *] },
end

noncomputable def eval₀ {σ ι α} [has_zero α] (s : BoundedStream σ ι α) : ι →₀ α :=
if s.now.ready then finsupp.single s.now.index s.now.value else 0

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
    simp [now, nr], } },
{ refl }
end

@[simp] lemma bound_delta_zero : s.bound = 0 → s.δ.bound = 0 := λ _, by simp [δ, *]
@[simp] lemma bound_delta_succ {n : ℕ} : s.bound = n.succ → s.δ.bound = n := λ _, by simp [δ, *]

lemma eval_identity : s.eval = s.eval₀ + s.δ.eval := begin
simp [eval, eval'],
cases em (s.bound = 0),
{ simp [h, eval'], },
{ obtain ⟨_, this⟩ := nat.exists_eq_succ_of_ne_zero h,
  rw [this, eval', bound_delta_succ s this] }
end

variables {σ₁ σ₂ : Type}
(a : BoundedStream σ₁ ι α)
(b : BoundedStream σ₂ ι α)
--(b : BoundedStream σ₂ ι β)
(s₁ : σ₁) (s₂ : σ₂)

noncomputable def state_le {α β : Type} (a : BoundedStream σ₁ ι α) (b : BoundedStream σ₂ ι β)
: σ₁ × σ₂ → bool :=
λ s, a.index s.1 < b.index s.2 ∨ (a.index s.1 = b.index s.2 ∧ a.ready s.1 ≤ b.ready s.2)

def state_lt {α β : Type} (a : BoundedStream σ₁ ι α) (b : BoundedStream σ₂ ι β)
: σ₁ × σ₂ → Prop :=
λ s, a.index s.1 < b.index s.2 ∨ (a.index s.1 = b.index s.2 ∧ a.ready s.1 < b.ready s.2)

instance : preorder (BoundedStream σ ι α) :=
{le := λ a b, state_le a b (a.state, b.state),
 le_refl := by simp [state_le],
 le_trans := begin simp [state_le], intros _ _ _ h1 h2, cases h1; cases h2, apply or.inl, apply lt_trans h1 h2, apply or.inl, rw ← h2.1, assumption, apply or.inl, rw h1.1, assumption, apply or.inr, split, exact eq.trans h1.1 h2.1,

apply h2.2 ∘ h1.2,
--apply le_trans h1.2 h2.2,

end
}

class Merge (σ : Type) := (merge : σ × σ → σ)

noncomputable def hmul
--{α β γ}
{α}
[has_mul α]
--[has_hmul α β γ]
(a : BoundedStream σ₁ ι α) (b : BoundedStream σ₂ ι α) : BoundedStream (σ₁ × σ₂) ι α :=
{ next  := λ s, if state_le a b s then (a.next s.1, s.2) else (s.1, b.next s.2),
  index := λ s, max (a.index s.1) (b.index s.2),
  value := λ s, (a.value s.1) * (b.value s.2),
  ready := λ s, a.ready s.1 ∧ b.ready s.2 ∧ (a.index s.1 = b.index s.2),
  valid := λ s, a.valid s.1 ∧ b.valid s.2,
  bound := a.bound + b.bound,
  state := (a.state, b.state),
  bound_valid := begin sorry end,
}

infix ` ⋆ `:71 := hmul

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

-- instance {α β γ} [has_hmul α β γ] : has_hmul (BoundedStream σ₁ ι α) (BoundedStream σ₂ ι β) (BoundedStream (σ₁ × σ₂) ι γ) := ⟨hmul⟩

#check le_max_of_le_left
instance {α} [has_mul α] : has_hmul (BoundedStream σ₁ ι α) (BoundedStream σ₂ ι α) (BoundedStream (σ₁ × σ₂) ι α) := ⟨hmul⟩

lemma hmul.ready : (a ⋆ b).now.ready = a.now.ready && b.now.ready && (a.now.index = b.now.index) := by simp [(⋆), now]
@[simp] lemma hmul.value : (a ⋆ b).now.value = a.now.value * b.now.value
:= by simp [(⋆), now]
@[simp] lemma hmul.index : (a ⋆ b).now.ready → (a ⋆ b).now.index = a.now.index := by simp [(⋆), now] {contextual := tt}

lemma mul_next_state : (a ⋆ b).next (s₁, s₂) = (a.next s₁, s₂) ∨
                       (a ⋆ b).next (s₁, s₂) = (s₁, b.next s₂) :=
begin
  simp only [(⋆), BoundedStream.hmul],
  cases a.state_le b (s₁, s₂); simp [prod.fst],
end

lemma mul_succ : (a ⋆ b).δ = a.δ ⋆ b ∨
                 (a ⋆ b).δ = a ⋆ b.δ :=
begin
  sorry,
end

end BoundedStream

inductive reachable (q : BoundedStream σ ι α) : BoundedStream σ ι α → Type
| refl : reachable q
| step {r} : reachable r → reachable r.δ
noncomputable lemma reachable.δ {q r : BoundedStream σ ι α} : reachable q.δ r → reachable q r := λ path,
begin
induction path with _ _ h,
{ exact reachable.step reachable.refl },
{ exact reachable.step h }
end

class is_simple (q : BoundedStream σ ι α) : Prop :=
(monotonic : ∀ r, reachable q r → r ≤ r.δ)
--(monotonic : ∀ s, s ≤ (q.next s))
(reduced : ∀ s t, q.ready s → q.ready t → q.index s = q.index t → s = t)

variables {σ₁ σ₂ : Type}

open Stream
open BoundedStream

instance hmul.is_simple
(a : BoundedStream σ₁ ι α) (b : BoundedStream σ₂ ι α)
[is_simple a] [is_simple b] : is_simple (a ⋆ b) :=
⟨begin rintros ⟨s₁, s₂⟩,
   cases BoundedStream.mul_next_state a b s₁ s₂;
   { rw h, apply max_le_max; simp only [(⋆), hmul, index, is_simple.monotonic] },
 end,
 begin
   rintro ⟨s₁, s₂⟩ ⟨t₁, t₂⟩ aready bready ih,
   -- ready → ai₁ = bi₁, ai₂ = bi₂. index = index → ai₁ = ai₂. reduced a → s₁ = s₂, etc
   sorry
 end⟩

variables
(a : BoundedStream σ ι α) [is_simple a]
(b : BoundedStream σ ι α) [is_simple b]

section lemmas
variables {a} {b}
lemma state_le.le_of_not_le : ¬ a ≤ b → b ≤ a :=
begin
  intro h,
  simp [(≤), preorder.le, state_le, not_or_distrib] at h ⊢,
  have i_le : b.index b.state ≤ a.index a.state := h.1,
  cases le_iff_eq_or_lt.mp i_le with this this,
  { exact or.inr ⟨this, le_of_lt (lt_of_not_le (h.2 this.symm))⟩ },
  { exact or.inl this }
end

instance delta_is_simple {a :  BoundedStream σ ι α} [h : is_simple a] : is_simple a.δ :=
{ monotonic := λ r path, is_simple.monotonic r (reachable.δ path),
  .. h}

lemma mono_delta : a ≤ a.δ := is_simple.monotonic a reachable.refl
lemma terminal_eval_zero : a.bound = 0 → a.eval = 0 := λ h, by simp [eval, h, eval']

#check finsupp.fun_like
@[simp] lemma mul_zero_of_support_neq {i j : ι} {c d : α} : i ≠ j → finsupp.single i c * finsupp.single j d = 0 :=
begin
intros h,
ext,
simp [finsupp.single, finsupp.mul_apply],
intros,
cc,
end

@[simp] lemma mul_eq_support (i : ι) (c d : α) : finsupp.single i c * finsupp.single i d = finsupp.single i (c*d) :=
begin
  ext,
  simp [finsupp.single, finsupp.mul_apply] { contextual := tt},
end

@[simp] lemma mul_eval₀
(a : BoundedStream σ₁ ι α) (b : BoundedStream σ₂ ι α) : (a ⋆ b : BoundedStream _ _ α).eval₀ = a.eval₀ * b.eval₀ :=
begin
  simp [eval₀],
  split_ifs with h h1 h2; try {refl},

  { have h' := h,
    simp [hmul.ready] at h,
    have := h.2.2,
    simp [← this],
    simp [h'] },

  repeat
  { simp [hmul.ready] at *,
    cases_type* and,
    contradiction },
  simp [hmul.ready] at h,
  cases_type* and,
  have := h h_1 h_2,
  rw mul_zero_of_support_neq this,
end

--lemma lt_mul_is_zero  : a < b → a.eval₀ * b.eval = 0 := sorry
--lemma lt_mul_0_is_zero  : a < b → a.eval₀ * b.eval₀ = 0 := sorry
. /- todo: -/
lemma le_succ_is_left  : a ≤ b → (a ⋆ b).δ = a.δ ⋆ b :=
begin
intros h,
rw [(⋆), δ],
simp,
-- oops: need a.bound = 0 → a ≤ b → b.bound = 0
end
lemma le_succ_is_right : b ≤ a → (a ⋆ b).δ = a ⋆ b.δ := sorry
lemma reduced_mul_eval  : a ≤ b → a.eval₀ * b.eval₀ = a.eval₀ * b.eval := sorry
lemma reduced_mul_eval' : b ≤ a → a.eval₀ * b.eval₀ = a.eval * b.eval₀ := sorry
lemma terminal_zero_mul  : a.bound = 0 → (a ⋆ b : BoundedStream _ _ α).eval = 0 := sorry
lemma terminal_mul_zero  : b.bound = 0 → (a ⋆ b : BoundedStream _ _ α).eval = 0 := sorry
end lemmas


theorem mul_spec : (a ⋆ b : BoundedStream _ _ α).eval = a.eval * b.eval :=
begin
  unfreezingI { induction a using BoundedStream.stream_elim with a terminal a ih_a generalizing b},
  { simp [terminal_eval_zero terminal, terminal_zero_mul terminal] },
  { unfreezingI { induction b using BoundedStream.stream_elim with b terminal b ih_b },
    { simp [terminal_eval_zero terminal, terminal_mul_zero terminal] },
    { cases em (a ≤ b),
      { rw [a.eval_identity, (a ⋆ b : BoundedStream _ _ α).eval_identity],
        rw [right_distrib],
        rw [mul_eval₀ a b, reduced_mul_eval h, le_succ_is_left h, @ih_a delta_is_simple] },
      { have : b ≤ a := state_le.le_of_not_le h,
        rw [b.eval_identity, (a ⋆ b : BoundedStream _ _ α).eval_identity],
        rw [left_distrib],
        rw [mul_eval₀ a b, reduced_mul_eval' this, le_succ_is_right this, ih_b] } } },
end

. /-
independence lemmas
potential failure
merge valid-bound/ready?
turing.eval
elab as eliminator
-/ .
