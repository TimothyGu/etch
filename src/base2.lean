import tactic
import algebra algebra.group algebra.group.defs logic.relation order.lexicographic
import data
universes u v variables {α β : Type*}
def nat.decr : ℕ → ℕ | 0 := 0 | (n+1) := n
def elementary {I V : Type} [decidable_eq I] [add_monoid V] (i : I) (v : V) := λ j, if i = j then v else 0
instance unit.has_top : has_top unit := ⟨()⟩
inductive reduces {α : Type u} (r : α → α → Prop) : α → α → Type u
| refl {s} : reduces s s
| tail {a b c} : r a b → reduces b c → reduces a c
structure iter (σ I V : Type*) :=
  (δ' : function.End σ) (ι' : σ → I) (ν' : σ → V) (ready' : σ → bool)
structure stream (σ I V : Type*) extends iter σ I V :=  (q : σ)
-- stream with a mutable value and upper bound; represents transient state of nested streams
structure var    (σ I V : Type*) extends stream σ I V := (value : V) (init : σ) (size : ℕ)
instance iter.functor {σ I} : functor (iter σ I) :=
{map := λ {α β : Type} (f : α → β) (i : iter σ I α) , { i with ν' := f ∘ iter.ν' i } }
instance stream.functor {σ I} : functor (stream σ I) := {map := λ {α β : Type} f s, { s with to_iter := f <$> s.to_iter } }
instance var.functor {σ I} : functor (var σ I) := {
  map := λ {α β : Type} (f : α → β) (v : var σ I α), {v with to_stream := f <$> v.to_stream, value := f v.value} }
/- namespace -/ namespace iter
variables {σ I V : Type*} (a : iter σ I V) (s t : σ)
@[simp] def δ := a.δ' s
@[simp] def ι := a.ι' s
@[simp] def ν := a.ν' s
@[simp] def ready := a.ready' s
def reachable := relation.refl_trans_gen (λ s t, t = a.δ s)
variable [linear_order I]
def monotonic := ∀ (s t : σ), a.reachable s t → a.ι' s ≤ a.ι' t
end iter
/- namespace -/ namespace stream
variables {σ I V : Type} (s : stream σ I V)
@[simp] def δ (s : stream σ I V) : stream σ I V := { s with q := s.δ' s.q}
@[simp] def ι := s.ι' s.q
@[simp] def ν := s.ν' s.q
@[simp] def ready := s.ready' s.q
variables [decidable_eq I] [has_top I] [add_monoid V]
--@[simp] def semantics₁  : I → V := if s.ready && (s.ι ≠ ⊤) then elementary s.ι s.ν else 0
--@[simp] def semantics : stream σ I V → ℕ → I → V | _ 0 := 0
--| s (n+1) := s.semantics₁ + semantics s.δ n
--notation `⟦` s, k `⟧` := s.semantics k
variables [linear_order I]
@[simp] def monotonic := s.to_iter.monotonic
end stream
class to_array (α : Type) (β : out_param Type) := (arrange : α → β)
/- namespace -/ namespace var
variables {σ I V : Type} (s : var σ I V)
def δ : var σ I V := { s with to_stream := s.to_stream.δ, value := s.to_stream.δ.ν, size := s.size.decr }
@[simp] def ι := s.to_stream.ι
@[simp] def ν := s.value
def reset : var σ I V := { s with to_stream := { s with q := s.init } }
variables [decidable_eq I]
@[simp] def semantics₁ [add_monoid V] : I → V := if s.to_stream.ready then elementary s.ι s.ν else 0
@[simp] def semantics' [add_monoid V] : var σ I V → ℕ → I → V | _ 0 := 0
| v (n+1) := v.semantics₁ + v.δ.semantics' n
@[simp] def semantics [add_monoid V] (v : var σ I V) : I → V := v.semantics' v.size
instance scalar.to_array [add_monoid V] : to_array V V := ⟨id⟩
def arrange {V'} [add_monoid V'] [to_array V V'] : (var σ I V) → (I → V') :=
λ v, (to_array.arrange <$> v).semantics
structure var_state (σ V : Type*) := (value : V) (init : σ) (size : ℕ)
-- def bounded_mutable_stream (σ I V : Type*) := stream (σ × var_state σ V) I V
instance to_array {V'} [add_monoid V'] [to_array V V'] : to_array (var σ I V) (I → V') :=
{ arrange := var.arrange }
notation `⟦` v `⟧` := to_array.arrange v
end var

--def flatten {σ₁ I₁ σ₂ I₂} : stream σ₁ I₁ (stream σ₂ I₂ V) → stream

variables (v1 : var ℕ ℕ (var ℕ ℕ ℕ))
#check v1.δ.arrange
#check ⟦v1.δ⟧

inductive BinOp | add | mul | lt | eq | and | or | min
inductive LVal (γ : list Type) : Type → Type 1
| ident {i} : hmem i γ → LVal i
| value {σ I V : Type}   : LVal (var σ I V) → LVal V
inductive E (γ : list Type) : Type → Type 1
| ident {i} : hmem i γ → E i
| value {σ I V : Type}   : E (var σ I V) → E V
| current {σ I V : Type} : E (var σ I V) → E I
| ready {σ I V : Type}   : E (var σ I V) → E bool
| empty {σ I V : Type}   : E (var σ I V) → E bool
| tt : E bool
| ff : E bool
--| bin_op : BinOp → E → E → E
variable {γ : list Type}
-- lens:
def E.get (s : hlist γ) : Π {i}, E γ i → i
| _ (E.ident var) := s.get var
| _ (E.value e)   := e.get.ν
| _ (E.current e) := e.get.ι
| _ (E.ready e)   := e.get.to_stream.ready
| _ (E.empty e)   := e.get.size = 0
| _ (E.tt) := tt
| _ (E.ff) := ff
def E.put (s : hlist γ) : Π {i}, E γ i → i → hlist γ
| _ (E.ident var) := λ v, s.update v var
| _ (E.value e)   := λ v, e.put { e.get s with value := v }
| _ (E.current e) := λ _, s -- no
| _ (E.empty e)   := λ _, s -- no
| _ (E.ready e)   := λ _, s -- no
| _ (E.tt) := λ _, s -- no
| _ (E.ff) := λ _, s -- no
def label := string
inductive Prog (γ : list Type) : Type 1
| expr {i} (e : E γ i) : Prog
| accum {V} (f : V → V → V) (dst : E γ V) (val : E γ V) : Prog
| store {i} (dst : E γ i) (val : E γ i) : Prog
| next {σ I V : Type} (stream : E γ (var σ I V)) : Prog
| seq (a b : Prog) : Prog
| skip : Prog
| jump : label → Prog
| «if» : E γ bool → Prog → Prog → Prog
infixr ` <;> `:1 := Prog.seq
variables {σ I V : Type} (s : var σ I V)
@[simp] def E.next (x : E γ (var σ I V)) : Prog γ := Prog.next x
structure Gen (γ : list Type) (ι α : Type*) :=
(current : ι)
(value : α)
(ready : E γ bool)
(empty : E γ bool)
(next (ifEmpty : unit → Prog γ) (ifNonempty : Prog γ → Prog γ) : Prog γ)
(reset : Prog γ)
(initialize : Prog γ)

-- @[derive [decidable_eq, fintype]]
-- def BinOp.mk_type : BinOp → Type 1
-- | (BinOp.add) := Π{γ} {i: Type}, E γ i → E γ i → E γ i
-- | (BinOp.mul) := Π{γ} {i: Type}, E γ i → E γ i → E γ i
-- | (BinOp.lt)  := Π{γ} {i: Type}, E γ i → E γ i → E γ bool
-- | (BinOp.eq)  := Π{γ} {i: Type}, E γ i → E γ i → E γ bool
-- | (BinOp.and) := Π{γ} {i: Type}, E γ bool → E γ bool → E γ bool
-- | (BinOp.or)  := Π{γ} {i: Type}, E γ bool → E γ bool → E γ bool
-- | (BinOp.min) := Π{γ} {i: Type}, E γ i → E γ i → E γ i

-- def BinOp.mk : Π (b : BinOp), BinOp.mk_type b
-- | BinOp.and := λ γ i x y,
--   match x, y with
--   | E.tt, y := y
--   | x, E.tt := x
--   | x, y := E.bin_op BinOp.and x y
--   end
-- | BinOp.or := λ x y,
--   match x, y with
--   | E.false, y := y
--   | x, E.false := x
--   | E.true, _ := E.true
--   | _, E.true := E.true
--   | x, y := E.bin_op BinOp.or x y
--   end
-- | b := E.bin_op b
-- instance : has_coe_to_fun BinOp BinOp.mk_type := ⟨BinOp.mk⟩

-- def mulGen [has_mul α] (a b : Gen γ (E γ I) α) : Gen γ (E γ I) α :=
-- { current := BinOp.min a.current b.current,
--   value := a.value * b.value,
--   ready := BinOp.eq a.current b.current && a.ready && b.ready,
--   empty := a.empty || b.empty,
--   next := λ kn ks, Prog.if (a.empty || b.empty) (kn ()) $
--     Prog.if (BinOp.lt a.current b.current) (a.next kn ks) (b.next kn ks),
--   reset := a.reset <;> b.reset,
--   initialize := a.initialize <;> b.initialize }

namespace Prog
def blocks (γ : list Type) := label → Prog γ
@[reducible] def state (γ : list Type) := Prog γ × hlist γ
def step (b : blocks γ) (s : hlist γ) : Prog γ → (Prog γ × hlist γ)
| (next e) := (skip, e.put s (e.get s).δ)
| (store dst src) := (skip, dst.put s (src.get s))
| (accum f dst src) := (skip, dst.put s $ f (dst.get s) (src.get s))
| (skip <;> b) := (b, s)
| (a <;> b) := let (a', s') := a.step in (a' <;> b, s')
| (jump l) := (b l, s)
| («if» c t e) := (if c.get s then t else e, s)
| (skip) := (skip, s)
| (expr _) := (skip, s) -- todo?
def reachable {γ} (b : blocks γ) : state γ → state γ → Type* :=
reduces (λ (p t : state γ), t = Prog.step b p.2 p.1)
variables (prog : blocks γ)
example (s : Prog γ × hlist γ) : reachable prog s s := reduces.refl
end Prog

section semantics
variables (prog : Prog.blocks γ)

def externGen {σ} {γ} (x : E γ (var σ I V)) : Gen γ (E γ I) (E γ V) :=
{ current    := x.current,
  value      := x.value,
  ready      := E.tt,
  empty      := x.empty,
  next       := λ kn ks, Prog.if x.empty (kn ()) (ks x.next),
  reset      := sorry, -- Prog.expr $ call "reset",
  initialize := Prog.skip }

def var_iter (x : E γ (var σ I V)) : iter (hlist γ) I V :=
{ δ' := λ s, if x.empty.get s then s else (x.next.step prog s).2,
  ι' := λ s, x.current.get s,
  ν' := λ s, x.value.get s,
  ready' := λ _, tt
}

def implements {σ : Type*} (g : Gen γ (E γ I) (E γ V)) (s : iter σ I V)
(st : hlist γ) (st' : σ) : Prop
:= (g.current.get st = s.ι st')
∧  (g.ready.get st = s.ready st')
∧  (s.ready st' → g.value.get st = s.ν st')
def reachable_state {γ : list Type} (prog : Prog.blocks γ) (p : Prog γ) (s s' : hlist γ) : Prop :=
nonempty (Prog.reachable prog (p,s) (p,s'))
def simulates {σ : Type*} (g : Gen γ (E γ I) (E γ V)) (i : iter σ I V) (loop done : label)
(st : hlist γ) (st' : σ) : Prop := implements g i st st' → ∃ st'' : hlist γ,
reachable_state /-no-/prog
  (g.next (λ _, Prog.jump done) (<;> Prog.jump loop))
  st st'' ∧
implements g i st'' st'


def extend {α β} [decidable_eq α] (m : α → β) (k : α) (v : β) := λ k', if k = k' then v else m k'
notation m `⟦` k `↦` v `⟧` := extend m k v

def loopGen {γ : list Type} (loop done : label) (g : Gen γ (E γ I) (E γ V)) :=
g.next (λ _, Prog.jump done) (<;> Prog.jump loop)

def loopGenProg {γ : list Type} (prog : Prog.blocks γ) (loop done : label) (g : Gen γ (E γ I) (E γ V)) :=
prog⟦loop ↦ loopGen loop done g⟧⟦done ↦ Prog.skip⟧

theorem extern_sound (x : E γ (var σ I V)) (st : hlist γ) :
implements (externGen x) (var_iter prog x) st st := begin
simp [implements, externGen, var_iter, E.get],
end

lemma get_put {st : hlist γ} {α : Type} {y} (v : α) : (E.ident y).get ((E.ident y).put st v) = v := begin
simp only [E.get, E.put, hlist.update, hlist.get],
rw hlist.get_update,
end
lemma get_put_value {st : hlist γ} {α β : Type} (e : E γ (var α β V)) (v : V) : e.value.get (e.value.put st v) = v := begin
simp only [E.get, E.put, hlist.update, hlist.get, stream.ν],
sorry,
end

lemma var_form {α β : Type} (x : E γ (var σ I V)) : (∃ n, x = E.ident n) ∨ (∃ e : E γ (var α β (var σ I V)), x = e.value) := sorry

theorem extern_step_sound (x : E γ (var σ I V)) (st : hlist γ) (loop done : label) :
loop ≠ done → x.empty.get st = ff →
∃ st' : hlist γ,
reachable_state (loopGenProg prog loop done $ externGen x) (loopGen loop done $ externGen x) st st' ∧
x.get st' = (x.get st).δ :=
begin
  intros neq hnonempty,
  existsi _,
  split,
  { simp [reachable_state, loopGen, loopGenProg, externGen],
    apply nonempty.intro,
    apply reduces.tail,
    simp only [Prog.step],
    rw hnonempty, simp,
    apply reduces.tail,
    simp only [Prog.step],
    apply reduces.tail,
    simp only [Prog.step],
    apply reduces.tail,
    simp only [Prog.step, extend],
    simp only [if_true, eq_self_iff_true],
    split_ifs, {exfalso, exact neq h.symm},
    exact reduces.refl,
  },
  cases var_form x,
  { rw h.some_spec,
    rw [get_put],
  },
  { rw h.some_spec,
    rw [get_put_value], -- not correct
    exact ℕ, -- hmm
    exact ℕ,
  },
end

example : Gen γ (E γ I) (E γ V) → var (Prog γ × hlist γ) I V := sorry

variables {σ₁ σ₂ I₁ I₂ V₁ V₂ V₃ : Type} [linear_order I] [linear_order I₁] [linear_order I₂] (a : iter σ₁ I V₁) (b : iter σ₂ I V₂)
variable (mul : V₁ → V₂ → V₃)

variable (mulGen {γ γ'} (a : Gen γ (E γ I) (E γ V₁)) (b : Gen γ' (E γ' I) (E γ' V₂))
: Gen (γ++γ') (E (γ++γ') I) (E (γ++γ') V₃))
--variable (mulGen (a : Gen γ (E γ I) (E γ V₁)) (b : Gen γ (E γ I) (E γ V₂)) : Gen γ (E γ I) (E γ V₃))

def mul_iter (a : iter σ₁ I V₁) (b : iter σ₂ I V₂) : iter (σ₁×σ₂) I V₃ :=
{ δ' := λ ⟨s,t⟩, if a.ι s < b.ι t then (a.δ s,t) else if a.ι s > b.ι t then (s, b.δ t) else (a.δ s, b.δ t),
  ι' := λ ⟨s,t⟩, min (a.ι s) (b.ι t),
  ν' := λ ⟨s,t⟩, mul (a.ν s) (b.ν t),
  ready' := λ ⟨s,t⟩, (a.ι s) = (b.ι t),
}

def mk_mul (a : stream σ₁ I V₁) (b : stream σ₂ I V₂) : stream (σ₁×σ₂) I V₃ :=
⟨ mul_iter mul a.to_iter b.to_iter, (a.q, b.q) ⟩

theorem mul_step_sound {γ'} (st : hlist γ) (st' : hlist γ') (σs σt : σ) (loop done : label)
(prog : Prog.blocks (γ ++ γ'))
(a : Gen γ  (E γ I) (E γ V₁))
(b : Gen γ' (E γ' I) (E γ' V₂))
(s : iter σ I V₁)
(t : iter σ I V₂)
-- (ha : implements a s st σs)
-- (hb : implements b t st' σt)
:
loop ≠ done →
∃ st'' : hlist (γ ++ γ'),
reachable_state (loopGenProg prog loop done $ mulGen a b) (loopGen loop done $ mulGen a b) (st.append st') st'' ∧
sorry = (mk_mul (s.get st) (t.get st')).δ /- extract state of (mulGen a b) from st'', compare to -/
:=
begin

end

#check @mulGen
def mul_sound {γ'} {st : hlist γ} {st' : hlist γ'} {σs σt : σ}
(a : Gen γ (E γ I) (E γ V₁)) (s : iter σ I V₁)
(b : Gen γ (E γ I) (E γ V₂)) (t : iter σ I V₂)
(ha : implements a s st σs)
(hb : implements b t st σt) :
implements (mulGen a b) (mul_iter mul s t) st (σs, σt) := begin
split,
simp [implements, mulGen, mul_iter, E.get],

end

end semantics

namespace Prog
attribute [refl] reduces.refl
variables {r : α → α → Prop} {a b c : α}
@[trans] def trans (hab : reduces r a b) (hbc : reduces r b c) : reduces r a c :=
begin
  induction hab generalizing c,
  case reduces.refl { assumption },
  case reduces.tail : d e f rde hef h { exact reduces.tail rde (h hbc) }
end
end Prog

-- . update on component.
-- empty → reduces to skip
-- create LVal type?
-- step_block_lemma?
-- store as a Prop?

/-
σ → σ
σ → (I → V) × σ
σ → exp(σ, σ)
σ → _ × exp(σ, σ)
σ → F σ
F t := t × (I → V) × I (× bool ?)
-/
