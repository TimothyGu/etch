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

instance option.add_zero_class {α} : add_zero_class (option α) :=
⟨none, (<|>), option.none_orelse, option.orelse_none⟩

instance {α} : add_monoid (option α) :=
{ option.add_zero_class with
  add_assoc := by { intros, cases a; cases b; cases c; simp [add_zero_class.add] } }
example : add_zero_class heap := infer_instance
example : add_monoid heap := infer_instance

lemma merge_def {h₁ h₂ : heap} {x} : (h₁ + h₂) x = option.orelse (h₁ x) (h₂ x) := rfl

namespace heap
variables (P Q H₁ H₂ H₃ : set heap) {h₁ h₂ h₃ : heap}

@[simp] lemma option.none_eq_zero {α} : (none : option α) = 0 := rfl
@[simp] lemma option.not_some_eq_zero {α} (x : α) : some x ≠ 0 := λ h, by injection h
@[simp] lemma option.some_add_some {α} (x y : α) : some x + some y = some x := rfl
@[simp] lemma option.none_add {α} (x : option α) : none + x = x := by cases x; simp [option.none_eq_zero]

lemma option.add_eq_zero_iff {α} (x y : option α) : x + y = 0 ↔ x = 0 ∧ y = 0 :=
by cases x; cases y; simp

lemma orelse_neq_zero (h₁ h₂ : heap) (x) : x ∈ h₁.support ∪ h₂.support ↔ h₁ x + h₂ x ≠ 0 :=
by simp only [option.add_eq_zero_iff, or_iff_not_imp_left, finset.mem_union, finsupp.mem_support_iff, ne.def, not_not, not_and]

theorem support_eq (h₁ h₂ : heap) : (h₁ + h₂).support = h₁.support ∪ h₂.support :=
by simp [has_add.add, finsupp.zip_with, finsupp.support_on_finset, finset.filter_eq_self, orelse_neq_zero]

def disjoint' (h₁ h₂ : heap) : Prop := ∀ loc, h₁ loc = none ∨ h₂ loc = none
def disjoint  (h₁ h₂ : heap) : Prop := disjoint h₁.support h₂.support

infix  ` # `:80  := disjoint

#check set.inter_Inter
#check finset.disj_union_eq_union
lemma disjoint_equiv : h₁ # h₂ ↔ disjoint' h₁ h₂ :=
{ mp  := begin intros h l, simp [disjoint, _root_.disjoint] at *, sorry end,
  mpr := sorry
}

def star : hprop := λ h, ∃ (h₁ h₂ : heap),
def star : set heap := λ h, ∃ (h₁ h₂ : heap),
H₁ h₁ ∧ H₂ h₂ ∧ disjoint h₁ h₂ ∧ h = h₁ + h₂

infixr ` ⋆ `:71 := star

def eval : Prog → heap → heap .

def hoare (p : Prog) (P Q : set heap) : Prop :=
∀ s, P s → Q (eval p s)

def triple (t : Prog) (P Q : set heap) : Prop :=
∀ H, hoare t (P ⋆ H) (Q ⋆ H)

lemma disjoint.comm {h₁ h₂} : h₁ # h₂ = h₂ # h₁ := by simp [heap.disjoint, disjoint.comm]

lemma disjoint.add_comm {h₁ h₂} : h₁ # h₂ → h₁ + h₂ = h₂ + h₁ := begin
intros dis,
have dis' := disjoint_equiv.mp dis,
ext l,
cases dis' l; simp only [h, finsupp.coe_add, pi.add_apply, option.none_eq_zero, zero_add, add_zero]
end

lemma star.symm : ∀ x, (H₁ ⋆ H₂) x → (H₂ ⋆ H₁) x := begin
simp only [star],
rintro x ⟨h₁, h₂, p1, p2, dis, split⟩,
refine ⟨h₂, h₁, p2, p1, dis.symm, _⟩,
{ rw dis.add_comm at split, assumption }
end

theorem star.comm : H₁ ⋆ H₂ = H₂ ⋆ H₁ := begin
ext,
split ; exact star.symm _ _ _,
end

lemma disjoint.sum_l  {h₁ h₂ h₃ : heap} : (h₁ + h₂) # h₃ ↔ h₁ # h₃ ∧ h₂ # h₃ := by simp [disjoint, support_eq]
lemma disjoint.sum_r {h₁ h₂ h₃ : heap} : h₁ # (h₂ + h₃) ↔ h₁ # h₂ ∧ h₁ # h₃ := by simp [disjoint, support_eq]

theorem star_assoc' : ∀ x, ((H₁ ⋆ H₂) ⋆ H₃) x → (H₁ ⋆ (H₂ ⋆ H₃)) x := begin
simp only [star],
rintro x ⟨_, h₃, ⟨h₁,h₂,p1,p2,dis12,split1'⟩, p3, dis3, splitx⟩,
rw split1' at dis3,
obtain ⟨dis13, dis23⟩ := (disjoint.sum_l.mp dis3),
refine ⟨h₁, (h₂ + h₃), p1, ⟨h₂, h₃, p2, p3, dis23, rfl⟩, _, _⟩,
{ simp [disjoint.sum_r, *] },
{ simp [split1', splitx, add_assoc] }
end

theorem star_assoc : (H₁ ⋆ H₂) ⋆ H₃ = H₁ ⋆ (H₂ ⋆ H₃) := begin
ext,
refine ⟨star_assoc' _ _ _ x, _⟩,
intro h,
rw [star.comm, star.comm H₂ H₃] at h,
have := star_assoc' _ _ _ x h,
rw star.comm, rw star.comm H₁ H₂, assumption,
end

def frame : ∀ (t : Prog) H, triple t P Q → triple t (P ⋆ H) (Q ⋆ H) := begin
intros _ _ h,
simp only [triple, star_assoc] at *,
intro _,
exact h _,
end

end heap
