import verify

variables {α ι γ β : Type}
variables (R : Type) [add_zero_class R] [has_one R] [has_mul R]

def rev_fmap_comp {f} [functor f] (x : α → f β) (y : β → f γ) := functor.map y ∘ x
infixr ` ⊚ `:90 := rev_fmap_comp
def rev_app : α → (α → β) → β := function.swap ($)
infixr ` & `:9 := rev_app

variable {R}

def index.zero : Expr R := Expr.lit (ExprVal.nat 0)
def index.one : Expr R := Expr.lit (ExprVal.nat 1)
def value.one : Expr R := Expr.lit (ExprVal.rval 1)
class has_hmul (α β : Type*) (γ : out_param Type*) :=
  (mul : α → β → γ)
instance hmul_of_mul {α : Type*} [has_mul α] : has_hmul α α α := ⟨has_mul.mul⟩
infix ` ⋆ `:71 := has_hmul.mul

def Ident.access : Ident → Expr R → Expr R := Expr.access
def Ident.ident  : Ident → Expr R := Expr.ident

namespace Expr
@[pattern] def false : Expr R := Expr.lit (ExprVal.nat 0)
@[pattern] def true  : Expr R := Expr.lit (ExprVal.nat 1)

def neg : Expr R → Expr R
| (Expr.true) := Expr.false
| (Expr.false) := Expr.true
| e := Expr.call Op.not ![e]
-- def store   : Expr R → Expr R → Prog R := Prog.store
end Expr

notation a ` ⟪+⟫ `:80 b := Expr.call Op.add ![a, b]
notation a ` ⟪*⟫ `:80 b := Expr.call Op.mul ![a, b]
notation a ` ⟪-⟫ `:80 b := Expr.call Op.sub ![a, b]
notation a ` ⟪&&⟫ `:80 b := Expr.call Op.and ![a, b]
notation a ` ⟪||⟫ `:80 b := Expr.call Op.or ![a, b]
notation a ` ⟪<⟫ `:80 b := Expr.call Op.lt ![a, b]
notation a ` ⟪=⟫ `:80 b := Expr.call Op.eq ![a, b]
notation a ` ⟪/=⟫ `:80 b := Expr.neg $ Expr.call Op.eq ![a, b]
infixr ` ⟪;⟫ `:1 := Prog.seq
notation a ` ::= `:20 c := Prog.store a none c
@[pattern] def Expr.le : Expr R → Expr R → Expr R := λ a b, (a ⟪<⟫ b) ⟪||⟫ (a ⟪=⟫ b)
notation  a ` ⟪≤⟫ `:71 b := Expr.le a b
infix `∷`:9000 := Ident.mk

def Prog.accum      : Ident → option (Expr R) → Expr R → Prog R := λ name i v, Prog.store name i (v ⟪+⟫ name.ident)
def Ident.increment : Ident → Prog R := λ v, Prog.store v none (v ⟪+⟫ index.one)
def Expr.succ : Expr R → Expr R := λ e, e ⟪+⟫ index.one

def min : Expr R → Expr R → Expr R := λ a b, Expr.call Op.min ![a, b]
def max : Expr R → Expr R → Expr R := λ a b, Expr.call Op.max ![a, b]

def mul [has_hmul α β γ] (a : BoundedStreamGen R (Expr R) α) (b : BoundedStreamGen R (Expr R) β) : BoundedStreamGen R (Expr R) γ :=
{ current := max a.current b.current,
  value := a.value ⋆ b.value,
  ready := a.ready ⟪&&⟫ b.ready ⟪&&⟫ a.current ⟪=⟫ b.current,
  next  := Prog.branch (a.current ⟪<⟫ b.current ⟪||⟫
                   (a.current ⟪=⟫ b.current ⟪&&⟫ a.ready.neg))
                        a.next
                        b.next,
  valid := a.valid ⟪&&⟫ b.valid,
  initialize  := a.initialize ⟪;⟫ b.initialize,
  bound := sorry,
}

instance [has_hmul α β γ] : has_hmul
  (BoundedStreamGen R (Expr R) α)
  (BoundedStreamGen R (Expr R) β)
  (BoundedStreamGen R (Expr R) γ) := ⟨mul⟩

variables (R)
structure AccessExpr := (base : Ident) (index : Expr R)

variables {R}

def AccessExpr.store : AccessExpr R → Expr R → Prog R := λ e, Prog.store e.base e.index
def AccessExpr.accum : AccessExpr R → Expr R → Prog R := λ e, Prog.store e.base e.index
def AccessExpr.expr  : AccessExpr R → Expr R := λ e, Expr.access e.base e.index

section csr_lval
variables (R)

@[reducible] def loc := Expr
structure il :=
  (crd  : loc R → Expr R)
  (push : Expr R → (loc R → Prog R) → Prog R × loc R)
structure vl (α : Type) :=
  (pos  : loc R → α)
  (init : loc R → Prog R)
structure lvl (α : Type) extends (il R), (vl R α).
instance : functor (lvl R) := { map := λ _ _ f l, { l with pos := f ∘ l.pos } }

variables {R}
def sparse_index (indices : Ident) (bounds : AccessExpr R × AccessExpr R) : il R :=
let (lower, upper) := bounds, -- upper := uv.access ui, lower := lv.access li,
     current := indices.access (upper.expr ⟪-⟫ index.one) in
let loc := upper.expr ⟪-⟫ index.one in
{ crd  := indices.access,
  push := λ i init,
    let prog := Prog.if1 (lower.expr ⟪=⟫ upper.expr ⟪||⟫ i ⟪/=⟫ current)
                      ((upper.accum index.one) ⟪;⟫ init loc) ⟪;⟫
                Prog.store indices (upper.expr ⟪-⟫ index.one) i
    in (prog, loc) }

variable {R}

def dense_index (dim : Expr R) (counter : Ident) (base : Expr R) : il R :=
{ crd  := id,
  push := λ i init,
    let l i  : loc R  := base ⟪*⟫ dim ⟪+⟫ i,
        prog : Prog R := Prog.loop (counter.ident ⟪≤⟫ i).to_loop_bound
                           (init (l counter) ⟪;⟫ counter.increment)
    in (prog, l i) }

def interval_vl (array : Ident) : vl R (AccessExpr R × AccessExpr R) :=
{ pos  := λ loc, (⟨array, loc⟩, ⟨array, loc.succ⟩),
  init := λ loc, (AccessExpr.mk array loc.succ).store (array.access loc) }

def dense_vl    (array : Ident) : vl R (Expr R) :=
{ pos  := λ loc, array.access loc,
  init := λ loc, (AccessExpr.mk array loc).store index.zero }

def implicit_vl : vl R (Expr R) := { pos := id, init := λ _, Prog.skip }

-- def base (array : E) : lvl E := { i_shift := λ _ i, array.access i,  }

-- this combinator combines an il with a vl to form a lvl.
-- the extra parameter α is used to thread the primary argument to a level through ⊚.
--   see dcsr/csr_mat/dense below
def with_values : (α → il R) → vl R β → α → lvl R β := λ i v e, lvl.mk (i e) v

def dense_mat (d₁ d₂ : Expr R) (ns : NameSpace) := index.zero &
  (with_values (dense_index d₁ (ns ∷ Vars.i)) implicit_vl) ⊚
  (with_values (dense_index d₂ (ns ∷ Vars.j)) $ dense_vl (ns ∷ Vars.x))

-- def sparse_vec (ns : NameSpace) := (0, ) &
--   (with_values (sparse_index "A1_crd") (dense_vl "A_vals"))

def dcsr (ns : NameSpace) : lvl R (lvl R (Expr R)) :=
  let coord1 := ns ∷ Vars.i, coord2 := ns ∷ Vars.j,
      pos1   := ns ∷ Vars.x, pos2 := ns ∷ Vars.y,
      vals   := ns ∷ Vars.w
  in
    (interval_vl pos1).pos index.zero &
      (with_values (sparse_index coord1) (interval_vl pos2)) ⊚
      (with_values (sparse_index coord2) (dense_vl vals))

def csr (d : Expr R) (ns : NameSpace) : lvl R (lvl R (Expr R)) :=
  let i    := ns ∷ Vars.i, coord2 := ns ∷ Vars.j,
      pos2 := ns ∷ Vars.y, vals   := ns ∷ Vars.w
  in index.zero &
      (with_values (dense_index d i) (interval_vl pos2)) ⊚
      (with_values (sparse_index coord2) (dense_vl vals))

end csr_lval

variables (R)
class Compile (l r : Type) := (compile : l → r → Prog R)

instance expr.compile : Compile R Ident (Expr R) :=
{ compile := λ l r, Prog.store l none r }

instance unit_compile [Compile R α β] : Compile R α (BoundedStreamGen R unit β) :=
{ compile := λ acc v,
    v.initialize ⟪;⟫ Prog.loop (v.valid.to_loop_bound)
      (Prog.if1 v.ready (Compile.compile acc v.value) ⟪;⟫ v.next) }

instance ind_compile [Compile R α β] : Compile R (lvl R α) (BoundedStreamGen R (Expr R) β) :=
{ compile := λ storage v,
    let (push_i, loc) := storage.push v.current storage.init in
    v.initialize ⟪;⟫
    Prog.loop (v.valid.to_loop_bound)
      (Prog.if1 v.ready (Compile.compile (storage.pos loc) v.value) ⟪;⟫ v.next) }
