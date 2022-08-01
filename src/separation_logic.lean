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

open_locale classical

--set_option trace.class_instances true

instance {α} : has_zero (option α) := ⟨none⟩
@[reducible] def heap := loc →₀ option value
def hprop := heap → Prop

instance option.add_zero_class {α} : add_zero_class (option α) :=
⟨none, (<|>), option.none_orelse, option.orelse_none⟩

instance {α} : add_monoid (option α) :=
{ option.add_zero_class with
  add_assoc := by { intros, cases a; cases b; cases c; simp [add_zero_class.add] } }
example : add_zero_class heap := infer_instance
example : add_monoid heap := infer_instance

@[simp] lemma ne_zero_add_ne_zero {α} : ∀ (x y : option α), x ≠ 0 → x + y ≠ 0 :=  begin
intros _ _ h,
cases x; cases y; simp [(+), add_zero_class.add, has_zero.zero, add_zero_class.zero] at *,
exact h,
end

@[simp] lemma add_ne_zero_ne_zero {α} : ∀ (x y : option α), y ≠ 0 → x + y ≠ 0 :=  begin
intros _ _ h,
cases x; cases y; simp [(+), add_zero_class.add, has_zero.zero, add_zero_class.zero] at *,
exact h,
end

namespace heap
variables (P Q H₁ H₂ H₃ : hprop) {h₁ h₂ h₃ : heap}

lemma orelse_neq_zero : ∀ x ∈ h₁.support ∪ h₂.support, h₁ x + h₂ x ≠ 0 := begin
intros x h, simp only [finset.mem_union] at h,
cases h,
have := (h₁.mem_support_to_fun x).mp h,
apply ne_zero_add_ne_zero, exact this,
have := (h₂.mem_support_to_fun x).mp h,
apply add_ne_zero_ne_zero, exact this,
end

theorem support_eq (h₁ h₂ : heap) : (h₁ + h₂).support = h₁.support ∪ h₂.support := begin
-- /-try this:-/ haveI := @ne.decidable (option value) (λ a b, classical.prop_decidable (a = b)),
simp only [has_add.add],
simp only [finsupp.zip_with, finsupp.support_on_finset],
have := λ a, @orelse_neq_zero h₁ h₂ a,
simp only [(+)] at this,
have := (finset.filter_eq_self (h₁.support ∪ h₂.support)).mpr this,
exact this, -- invalid type ascription, different decidable instances
sorry,
end

def disjoint' (h₁ h₂ : heap) : Prop := ∀ loc, h₁ loc = none ∨ h₂ loc = none
def disjoint  (h₁ h₂ : heap) : Prop := disjoint h₁.support h₂.support

infix  ` # `:80  := disjoint

lemma disjoint_equiv : h₁ # h₂ ↔ disjoint' h₁ h₂ :=
{ mp  := begin intros h l, simp [disjoint] at *, sorry end,
  mpr := sorry
}

--def merge : heap → heap → heap := (+)
--@[simp] lemma merge_is_add : merge h₁ h₂ = h₁ + h₂ := rfl

def star : hprop := λ h, ∃ (h₁ h₂ : heap),
H₁ h₁ ∧ H₂ h₂ ∧ disjoint h₁ h₂ ∧ h = h₁ + h₂

infixr ` ⋆ `:71 := star

def eval : Prog → heap → heap .

def hoare (p : Prog) (P Q : hprop) : Prop :=
∀ s, P s → ∃ s', eval p s = s' ∧ Q s'

def triple (t : Prog) (P Q : hprop) : Prop :=
∀ H, hoare t (P ⋆ H) (Q ⋆ H)

def hprop_ext : (∀ x, H₁ x ↔ H₂ x) → H₁ = H₂ := begin intro h, ext, exact h x end

lemma disjoint.comm {h₁ h₂} : h₁ # h₂ = h₂ # h₁ := by simp [heap.disjoint, disjoint.comm]

@[simp] lemma merge_eq {h₁ h₂ : heap} {x} : (h₁ + h₂) x = option.orelse (h₁ x) (h₂ x) := rfl

lemma disjoint.add_comm {h₁ h₂} : h₁ # h₂ → h₁ + h₂ = h₂ + h₁ := begin
intros dis,
have dis' := disjoint_equiv.mp dis,
ext l,
cases dis' l; simp [h],
end

lemma star.symm : ∀ x, (H₁ ⋆ H₂) x → (H₂ ⋆ H₁) x := begin
simp only [star],
rintro x ⟨h₁, h₂, p1, p2, dis, split⟩,
refine ⟨h₂, h₁, p2, p1, dis.symm, _⟩,
{ rw dis.add_comm at split, assumption }
end

theorem star.comm : H₁ ⋆ H₂ = H₂ ⋆ H₁ := begin
apply hprop_ext,
intro h,
split ; exact star.symm _ _ _,
end

lemma disjoint.sum_l  {h₁ h₂ h₃ : heap} : (h₁ + h₂) # h₃ ↔ h₁ # h₃ ∧ h₂ # h₃ := by simp [disjoint, support_eq]
lemma disjoint.sum_r {h₁ h₂ h₃ : heap} : h₁ # (h₂ + h₃) ↔ h₁ # h₂ ∧ h₁ # h₃ := by simp [disjoint, support_eq]

theorem star_assoc' : ∀ x, ((H₁ ⋆ H₂) ⋆ H₃) x → (H₁ ⋆ (H₂ ⋆ H₃)) x := begin
simp only [star],
rintros x ⟨h₁', h₃, ⟨h₁,h₂,p1,p2,dis12,split1'⟩, p3, dis3, splitx⟩,
rw split1' at dis3,
obtain ⟨dis13, dis23⟩ := (disjoint.sum_l.mp dis3),
refine ⟨h₁, (h₂ + h₃), p1, ⟨h₂, h₃, p2, p3, dis23, rfl⟩, _, _⟩,
{ simp [disjoint.sum_r, *] },
{ simp [split1', splitx, add_assoc] }
end

theorem star_assoc : (H₁ ⋆ H₂) ⋆ H₃ = H₁ ⋆ (H₂ ⋆ H₃) := begin
apply hprop_ext, intro x, refine ⟨star_assoc' _ _ _ x, _⟩,
{ intro h, rw star.comm at h, rw star.comm H₂ H₃ at h,
  have := star_assoc' _ _ _ x h,
  rw star.comm, rw star.comm H₁ H₂, assumption }
end

def frame : ∀ (t : Prog) H, triple t P Q → triple t (P ⋆ H) (Q ⋆ H) := begin
intros _ _ h,
simp only [triple, star_assoc] at *,
intro H',
exact h _,
end

end heap
