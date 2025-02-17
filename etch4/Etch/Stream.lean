import Mathlib.Algebra.Ring.Basic
import Etch.C
import Etch.Op
import Etch.Basic

--notation "𝟚"  => Bool

-- marked irreducible later
def Var (α : Type _) := String
def Var.mk : String → Var α := id
def Var.toString : Var α → String := id
instance : Coe String (Var α) := ⟨Var.mk⟩

inductive E : Type → Type 1
| call {α β} (op : O α β) (args : (i : Fin op.arity) → E (op.argTypes i)) : E β
| var    : (v : Var α) → E α
| access : Var α → E ℕ → E α
| intLit : ℕ → E ℕ

def E.v (α) (v : String) : E α := E.var v

structure HeapContext where
  store : Var α → α
  heap : Var α → ℕ → α

def E.eval (c : HeapContext) : E α → α
| call f args => f.spec (λ i => (args i).eval c)
| var v => c.store v
| access arr arg => c.heap arr (arg.eval c)
| intLit x => x

instance : OfNat Bool (nat_lit 0) := ⟨ false ⟩
instance : OfNat Bool (nat_lit 1) := ⟨ .true ⟩
instance [Tagged α] [Add α] : Add (E α) := ⟨ λ a b => E.call O.add ![a, b] ⟩
instance [Tagged α] [Sub α] : Sub (E α) := ⟨ λ a b => E.call O.sub ![a, b] ⟩
instance [Tagged α] [Mul α] : Mul (E α) := ⟨ λ a b => E.call O.mul ![a, b] ⟩
instance [Tagged α] [OfNat α (nat_lit 0)] : OfNat (E α) (nat_lit 0) := ⟨ E.call O.zero ![] ⟩
instance [Tagged α] [OfNat α (nat_lit 1)] : OfNat (E α) (nat_lit 1) := ⟨ E.call O.one ![] ⟩
instance : OfNat (E ℕ) n := ⟨ .intLit n ⟩
instance : Inhabited (E R) := ⟨ 0 ⟩
--def E.ext (f : String) : E Unit := E.call (O.voidCall f) ![]

def E.compile : E α → Expr
| @call _ _ op args => Expr.call op.name $ List.ofFn λ i => E.compile (args i)
| access base i => Expr.index (Expr.var base.toString) [i.compile]
| var v => Expr.var v.toString
| intLit x => Expr.lit x

infixr:40 " << " => λ a b => E.call O.lt ![a, b]
infixr:40 " <ᵣ " => λ a b => E.call O.ofBool ![E.call O.lt ![a, b]]
infixr:40 " == " => λ a b => E.call O.eq ![a, b]
infixr:40 " != " => λ a b => E.call O.neg ![(E.call O.eq ![a, b])]
infixr:40 " <= " => λ a b => E.call O.le ![a, b]

inductive P
| seq    : P → P → P
| while  : E Bool → P → P
| branch : E Bool → P → P → P
| skip   : P
| decl   : Var α → E α → P
| store_var : Var α → E α → P
| store_mem : Var α → E ℕ → E α → P

-- needs to come after P to avoid injectivity_lemma issue
attribute [irreducible] Var

def P.if1 := λ c t => P.branch c t P.skip
infixr:10 ";;" => P.seq

def P.compile : P → Stmt
| seq a b => Stmt.seq a.compile b.compile
| .while cond body => Stmt.while cond.compile body.compile
| branch c a b => Stmt.conde c.compile a.compile b.compile
| skip => Stmt.noop
| decl var e => Stmt.decl .Int var.toString e.compile
| store_var var e => Stmt.store (Expr.var var.toString) e.compile
| store_mem v l r => Stmt.store (Expr.index (Expr.var v.toString) [l.compile]) r.compile

def Name := List ℕ
def Name.toString : Name → String := "_".intercalate ∘ List.map (@ToString.toString ℕ _)
def Name.fresh (n : Name) (new : ℕ) := new :: n

structure S (ι : Type _) (α : Type _) where
  σ     : Type
  value : σ → α
  skip  : σ → E ι → P
  succ  : σ → P
  ready : σ → E Bool
  index : σ → E ι
  valid : σ → E Bool
  init  : Name → P × σ

infixr:25 " →ₛ " => S

section ι

variable {ι : Type} [Tagged ι] [DecidableEq ι] [LT ι] [DecidableRel (LT.lt : ι → ι → _)]

def Var.access (v : Var α) := E.access v
def Var.incr [Tagged α] [Add α] [OfNat α 1] (v : Var α) : P := .store_var v $ E.var v + 1
def Var.incr_array [Tagged α] [Add α] [OfNat α 1] (v : Var α) (ind : E ℕ) : P := .store_mem v ind $ v.access ind + 1
def Var.expr (v : Var α) : E α := E.var v
def Var.fresh (v : Var α) (n : Name) : Var α := Var.mk (v.toString ++ n.toString)
def Var.store_var (v : Var α) := P.store_var v
def Var.decl (v : Var α) := P.decl v

instance : Coe (Var α) (E α) := ⟨E.var⟩

instance : Functor (S ι) where map := λ f s => {s with value := f ∘ s.value }


def simpleSkip (pos : Var ℕ) (is : Var ι) (max_pos : E ℕ) (tgt : E ι) :=
  .store_var "temp" tgt;;
  .while ((pos.expr << max_pos) * (is.access pos << "temp")) pos.incr

def searchSkip (pos : Var ℕ) (is : Var ι) (max_pos : E ℕ) (i : E ι) : P :=
let hi : Var ℕ := "hi"; let lo : Var ℕ := "lo"; let m  : Var ℕ := "m";
let tgt : Var ι := "temp"; let not_done : Var Bool := "not_done"
tgt.store_var i;; .store_var lo pos;; .store_var hi max_pos;; .store_var not_done 1;;
(.while ((lo.expr <= hi.expr) * not_done) $
  .store_var m (E.call .mid ![lo.expr, hi.expr]) ;;
  .branch (.access is m << tgt.expr)
    (.store_var lo (m + 1))
    (.branch (tgt.expr << .access is "m")
      (.store_var hi (m - 1))
      ((.store_var not_done 0);; .store_var lo m))) ;;
  .store_var pos lo

inductive IterMethod | step | search

section Range
variable [LE ι] [DecidableRel (LE.le : ι → ι → _)]
def S.predRange [One α] (lower upper : E ι) : S ι α where
  σ := Var ι
  value   _ := 1
  succ    _ := .skip
  ready   _ := 1
  skip  pos := λ i => pos.store_var i
  index pos := pos
  valid pos := pos.expr << upper
  init  n   := let p := .fresh "pos" n; (p.decl lower, p)
end Range

def S.interval (h : IterMethod) (is : Var ι) (pos : Var ℕ) (lower upper : E ℕ) : S ι (E ℕ) where
  σ := Var ℕ
  value pos := pos.expr
  succ  pos := pos.incr
  ready pos := 1
  skip  pos := (match h with | .step => simpleSkip | .search => searchSkip)  pos is upper
  index pos := .access is pos.expr
  valid pos := pos.expr << upper
  init  n   := let p := pos.fresh n; (p.decl lower, p)

-- todo: use instead of zero
--class Bot (α : Type _) := (bot : α)
--notation "⊥"  => Bot.bot
def S.univ [Zero ι] [Add ι] [OfNat ι 1] (max l : Var ι) : S ι (E ι) where
  value last := last.expr
  succ  last := last.incr  -- imprecise but ok
  ready last := 1
  skip  last := λ i => .store_var last i
  index last := last.expr
  valid last := last.expr << max.expr
  init  n    := let v := l.fresh n; (v.decl 0, v)

def S.valFilter (f : α → E Bool) (s : ι →ₛ α) : ι →ₛ α :=
{ s with ready := λ p => s.ready p * f (s.value p),
         skip := λ p i =>
           .branch (s.ready p)
             (.branch (f (s.value p))
               (s.skip p i)
               (s.succ p;; s.skip p i))
             (s.skip p i) }

def dim : Var ι := "dim"

-- using fmap introduces a universe constraint between α and Type 1 (coming from E ι). this is probably ok anyway
--def S.repl' {α : Type 1} [Zero ι] (last : Var ι) (v : α) : S ι α := (Function.const _ v) <$> (S.univ last)
--def S.repl [Zero ι] (last : Var ι) (v : α) : S ι α := {S.univ last with value := λ _ => v}
def S.function [Zero ι] [Add ι] [OfNat ι 1] (last : Var ι) (f : E ι → α) : S ι α := f <$> S.univ dim last

structure csr (ι α : Type _) := (i : Var ι) (v : Var α) (var : Var ℕ)

def csr.of (name : String) (n : ℕ) (ι := ℕ) : csr ι ℕ :=
  let field {ι} (x : String) : Var ι := Var.mk $ name ++ n.repr ++ x
  { i := field "_crd", v := field "_pos", var := field "_i" }

def csr.level (h : IterMethod) : csr ι ℕ → E ℕ → S ι (E ℕ) := λ csr loc => S.interval h csr.i csr.var (.access csr.v loc) (csr.v.access (loc+1))
def S.level {f} [Functor f] (h : IterMethod) : csr ι ℕ → f (E ℕ) → f (S ι (E ℕ)) := Functor.map ∘ csr.level h
def S.leaf  {f} [Functor f] : Var α → f (E ℕ) → f (E α) := Functor.map ∘ E.access
--def S.leaf' : Var α → E ℕ → E α := E.access
def Contraction (α : Type _) := Σ ι, S ι α
instance : Functor Contraction where map := λ f ⟨ι, v⟩ => ⟨ι, f <$> v⟩
def S.contract (s : S ι α) : Contraction α := ⟨_, s⟩

end ι

def Fun (ι α : Type _) := E ι → α
infixr:25 " →ₐ "  => Fun -- arbitrarily chosen for ease of typing: \ra
example : (ℕ →ₐ ℕ →ₛ ℕ) = (ℕ →ₐ (ℕ →ₛ ℕ)) := rfl
def Fun.un (h : ι →ₐ α) : E ι → α := h
def Fun.of (h : E ι → α) : ι →ₐ α := h
instance : Functor (Fun ι) where map := λ f v => f ∘ v

def range : ℕ →ₐ E ℕ := id

def seqInit (a : S ι α) (b : S ι β) (n : Name) :=
let (ai, as) := a.init (n.fresh 0);
let (bi, bs) := b.init (n.fresh 1);
(ai ;; bi, (as, bs))
