import tactic.basic
import data.finsupp.indicator
import data.finset.preimage
import algebra.hom.group_action
import algebra.indicator_function
import order.bounded_order

noncomputable theory

-- todo
inductive loc
inductive value
inductive Prog
instance : decidable_eq loc := sorry

instance {α} : has_zero (option α) := ⟨none⟩
@[reducible] def heap := loc →₀ option value
def hprop := heap → Prop

instance option.add_zero_class : add_zero_class (option value) := ⟨none, (<|>), option.none_orelse, option.orelse_none⟩
instance : add_monoid (option value) := {
  option.add_zero_class with
  add_assoc := by { intros, cases a; cases b; cases c; simp [add_zero_class.add] } }
example : has_add heap := infer_instance
example : add_monoid heap := infer_instance


def eval : Prog → heap → heap .

namespace heap
variables (P Q H₁ H₂ H₃ : hprop) {h₁ h₂ h₃ : heap}

#check finsupp.zip_with
theorem support_eq (h₁ h₂ : heap) : (h₁ + h₂).support = h₁.support ∪ h₂.support := begin
simp [has_add.add, finsupp.zip_with, finsupp.support_on_finset],
-- rw finset.filter_true,
sorry
end

def disjoint' (h₁ h₂ : heap) : Prop := ∀ loc, h₁ loc = none ∨ h₂ loc = none
def disjoint  (h₁ h₂ : heap) : Prop := disjoint h₁.support h₂.support
lemma disjoint_equiv : disjoint h₁ h₂ ↔ disjoint' h₁ h₂ :=
{ mp  := begin intros h l, simp [disjoint] at *, sorry end,
  mpr := sorry
}
def merge : heap → heap → heap := has_add.add -- finsupp.zip_with option.orelse rfl


def star : hprop := λ h, ∃ (h₁ h₂ : heap),
H₁ h₁ ∧ H₂ h₂ ∧ disjoint h₁ h₂ ∧ h = merge h₁ h₂

infixr ` ⋆ `:71 := star

def hoare (p : Prog) (P Q : hprop) : Prop :=
∀ s, P s → ∃ s', eval p s = s' ∧ Q s'

def triple (t : Prog) (P Q : hprop) : Prop :=
∀ H, hoare t (P ⋆ H) (Q ⋆ H)

def hprop_ext : (∀ x, H₁ x ↔ H₂ x) → H₁ = H₂ := begin intro h, ext, exact h x end

lemma disjoint.symm {h₁ h₂} : disjoint h₁ h₂ → disjoint h₂ h₁ := begin
intros h, simpa [heap.disjoint, disjoint.comm]
end

--λ h l, (h l).swap

@[simp] lemma merge_eq {h₁ h₂ x} : (merge h₁ h₂) x = option.orelse (h₁ x) (h₂ x) := rfl

lemma disjoint.merge_eq {h₁ h₂} : disjoint h₁ h₂ → merge h₁ h₂ = merge h₂ h₁ := begin
intros dis,
have dis' := disjoint_equiv.mp dis,
ext l,
cases dis' l; simp [h],
end

lemma star_symm' : ∀ x, (H₁ ⋆ H₂) x → (H₂ ⋆ H₁) x := begin
simp only [star],
rintros x ⟨h₁, h₂, p1, p2, dis, split⟩,
refine ⟨h₂, h₁, p2, p1, dis.symm, _⟩,
{ rw dis.merge_eq at split, assumption }
end

theorem star_symm : H₁ ⋆ H₂ = H₂ ⋆ H₁ := begin
apply hprop_ext,
intro h,
split ; exact star_symm' _ _ _,
end

lemma disjoint.merge {h₁ h₂ h₃ : heap} : (h₁.merge h₂).disjoint h₃ → h₂.disjoint h₃ := begin
have := support_eq h₁ h₂,
simp [disjoint, merge, this],
end

theorem star_assoc' : ∀ x, ((H₁ ⋆ H₂) ⋆ H₃) x → (H₁ ⋆ (H₂ ⋆ H₃)) x := begin
simp only [star],
rintros x ⟨h₁', h₃, ⟨h₁,h₂,p1,p2,dis12,split1'⟩, p3, dis3, splitx⟩,
rw split1' at dis3,
refine ⟨h₁, (h₂.merge h₃), p1, ⟨h₂, h₃, p2, p3, disjoint.merge dis3, rfl⟩, _, _⟩,
{ simp [disjoint, merge] at dis3,
  simp [finsupp.support_add_eq dis12] at dis3,
  simp [disjoint, merge],
  simp [finsupp.support_add_eq dis3.2],
  exact ⟨dis12, dis3.1⟩ },
{ simp [split1', splitx, merge, add_assoc], }
end
theorem star_assoc : (H₁ ⋆ H₂) ⋆ H₃ = H₁ ⋆ (H₂ ⋆ H₃) := begin
apply hprop_ext, intro x, refine ⟨star_assoc' _ _ _ x, _⟩,
{ intro h, rw star_symm at h, rw star_symm H₂ H₃ at h,
  have := star_assoc' _ _ _ x h,
  rw star_symm, rw star_symm H₁ H₂, assumption }
end

def frame : ∀ (t : Prog) H, triple t P Q → triple t (P ⋆ H) (Q ⋆ H) := begin
intros _ _ h,
simp only [triple, star_assoc] at *,
intro H',
exact h _,
end


end heap
