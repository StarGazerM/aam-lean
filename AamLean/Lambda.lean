
import AamLean.Basic

import Aesop

namespace Lambda

notation "Var" => String

-- First we define the syntax of the lambda calculus
-- inductive EBool : Type where
--   | tru : EBool
--   | fls : EBool

inductive Expr : Type where
  | ref : Var → Expr
  | lam : Var → Expr → Expr
  | app : Expr → Expr → Expr
deriving BEq, DecidableEq, Repr

open Expr

-- use a list for the environment
-- inductive Env : Type where
--   | nil : Env
--   | cons : String → Value → Env → Env
-- def extend (x: String) (v: Value) (env: Env) : Env := Env.cons x v env

-- first try, using ℕ  for address in concrete semantics
notation "Addr" => Nat

-- envrioment is a map of var name to address
notation "Env" => List (Var × Addr)
-- def elookup (x: Var) : Env → Option Addr
--   | [] => none
--   | (y, a) :: rest => if x = y then some a else elookup x rest
@[aesop safe [constructors, cases]]
inductive env_lookup : Var → Env → Option Addr -> Prop where
  | elookup_nil : ∀ {x}, env_lookup x [] none
  | elookup_hit : ∀ {x a rest}, env_lookup x ((x, a) :: rest) (some a)
  | elookup_rest : ∀ {x y a a' rest},
      x ≠ y →
      env_lookup x rest a' ->
      env_lookup x ((y, a) :: rest) a'
@[aesop safe [constructors, cases]]
inductive env_update : Var → Addr → Env → Env → Prop where
  | env_update_nil : ∀ {x a},
    env_update x a [] [(x, a)]
  | env_update_hit : ∀ {x a rest},
    env_update x a ((x, _) :: rest) ((x, a) :: rest)
  | env_update_rest : ∀ {x y a a' rest rest'},
    env_update x a rest rest' →
    x ≠ y →
    env_update x a ((y, a') :: rest) ((y, a') :: rest')

-- some lemma about map lookup
theorem apply_env_empty : ∀ {x}, env_lookup x [] none := by aesop
theorem update_env_eq : ∀ {x a ρ ρ'},
  env_update x a ρ ρ' ->
  env_lookup x ρ' (some a) := by
  intro x a ρ ρ' h
  induction h
  . apply env_lookup.elookup_hit
  . apply env_lookup.elookup_hit
  . apply env_lookup.elookup_rest
    . assumption
    . assumption
theorem update_env_neq : ∀ {x y a ρ},
  x ≠ y →
  env_lookup x ρ v →
  env_lookup x ((y, a) :: ρ) v := by
  intros x y a ρ h₁ h₂
  apply env_lookup.elookup_rest
  assumption
  assumption
theorem update_env_shadow : ∀ {x a ρ ρ' ρ''},
  env_update x a ρ ρ' →
  env_update x b ρ' ρ'' →
  env_update x b ρ ρ'' := by
  admit



inductive Value : Type where
| col :  Expr → Env → Value
open Value
#check ((col (ref "x") ∅) : Value)

inductive Kont : Type where
  | mt : Kont
  | ar : Expr → Env → Addr → Kont
  | fn : Expr → Env → Addr → Kont

-- TODO: use Beq and generic AssocList for map
-- Store is a map of address to value
notation "VStore" => List (Addr × Value)
-- def slookup (x: Addr) : VStore → Option Value
--   | [] => none
--   | (y, v) :: rest => if x = y then some v else slookup x rest
inductive vs_lookup : Addr → VStore → Option Value ->Prop where
  | vslookup_nil : ∀ {x}, vs_lookup x [] none
  | vslookup_hit : ∀ {x y v rest}, x = y → vs_lookup x ((y, v) :: rest) (some v)
  | vslookup_rest : ∀ {x y v v' rest},
      x ≠ y →
      vs_lookup x rest v' ->
      vs_lookup x ((y, v) :: rest) v'
inductive vs_update : Addr → Value → VStore → VStore → Prop where
  | vs_update_nil : ∀ {x v},
    vs_update x v [] [(x, v)]
  | vs_update_hit : ∀ {x v rest},
    vs_update x v ((x, _) :: rest) ((x, v) :: rest)
  | vs_update_rest : ∀ {x y v v' rest rest'},
    vs_update x v rest rest' →
    x ≠ y →
    vs_update x v ((y, v') :: rest) ((y, v') :: rest')

-- for simple I separate the store of continuation from store of value
notation "KStore" => List (Addr × Kont)
-- def klookup (x: Addr) : KStore → Option Kont
--   | [] => none
--   | (y, v) :: rest => if x = y then some v else klookup x rest
inductive ks_lookup : Addr → KStore → Option Kont -> Prop where
  | ks_lookup_nil : ∀ {x}, ks_lookup x [] none
  | ks_lookup_hit : ∀ {x y v rest}, x = y → ks_lookup x ((y, v) :: rest) (some v)
  | ks_lookup_rest : ∀ {x y v v' rest},
      x ≠ y →
      ks_lookup x rest v' ->
      ks_lookup x ((y, v) :: rest) v'
inductive ks_update : Addr → Kont → KStore → KStore → Prop where
  | ks_update_nil : ∀ {x v},
    ks_update x v [] [(x, v)]
  | ks_update_hit : ∀ {x v rest},
    ks_update x v ((x, _) :: rest) ((x, v) :: rest)
  | ks_update_rest : ∀ {x y v v' rest rest'},
    ks_update x v rest rest' →
    x ≠ y →
    ks_update x v ((y, v') :: rest) ((y, v') :: rest')



-- Next we define the semantics of the lambda calculus
-- we use CESK* machine here

-- timestamp is nat keep increasing
notation "Time" => Nat

-- then we define the state of the machine
notation "Σ" => (Expr × Env × VStore × KStore × Addr × Time)

-- concrete tick
inductive Tick : Σ → Time → Prop where
  | tick : ∀ {e ρ σᵥ σₖ a t},
    Tick (e, ρ, σᵥ, σₖ, a, t) (t + 1)

-- concrete alloc function
inductive Alloc : Σ → Addr → Prop where
  | alloc : ∀ {e ρ σᵥ σₖ a t},
    Alloc (e, ρ, σᵥ, σₖ , a, t) t

open Kont

-- define the injection function
-- def inject (e: Expr) : Σ := (e, ∅, (∅, [(0, mt)]), 0, 0)
inductive inject : Expr → Σ → Prop where
  | inject : ∀ {e}, inject e (e, ∅, ∅, [(0, mt)], 0, 0)

-- def aeval (x: Var) (e: Env) (s: Store) : Option Value :=
--   match elookup x e with
--   | some a => value_lookup a s
--   | none => none
inductive aeval : Var → Env → VStore → Option Value → Prop where
  | aeval_hit : ∀ {x α v ρ σ},
      env_lookup x ρ (some α) →
      vs_lookup α s (some v) →
      aeval x ρ σ (some v)
  | aeval_var_miss : ∀ {x e s}, env_lookup x e none → aeval x e s none
  | aeval_addr_miss : ∀ {x α ρ σ},
      env_lookup x ρ (some α) →
      ks_lookup α s none → aeval x e σ none

-- def lambda_huh (v: Expr) : Bool :=
--   match v with
--   | lam _ _ => true
--   | _ => false
inductive lambda_huh : Expr → Prop where
  | lambda_huh : ∀ {x e}, lambda_huh (lam x e)

-- the small step semantics of the lambda calculus
inductive Eval : Σ → Σ → Prop where
  | eval_ref : ∀ {x ρ σᵥ σₖ a t},
    aeval x ρ σ (some (col v ρ')) →
    Eval (ref x, ρ, σᵥ, σₛ, a, t) (v, ρ', σᵥ, σₛ, a, t)
  | eval_app : ∀ {e₁ e₂ ρ σᵥ σₖ a t σₖ'},
    Alloc (app e₁ e₂, ρ, σᵥ, σₖ, a, t) b →
    Tick (app e₁ e₂, ρ, σᵥ, σₖ, a, t) u →
    ks_update b (ar e₁ ρ a) σₖ σₖ' →
    Eval (app e₁ e₂, ρ, σᵥ, σₖ, a, t)
         (e₁, ρ, σᵥ, σₖ, b, u)
  | eval_v_ar : ∀ {v ρ σᵥ σₖ a t σₖ'},
    lambda_huh v →
    Alloc (v, ρ, σᵥ, σₖ, a, t) b →
    Tick (v, ρ, σᵥ, σₖ, a, t) u →
    ks_lookup a σₖ (some (ar e ρ c)) →
    ks_update b (fn v ρ c) σₖ σₖ' →
    Eval (v, ρ, σᵥ, σₖ, a, t) (e, ρ, σᵥ, σₖ', b, u)
  | eval_v_fn : ∀ {v ρ σᵥ σₖ a t ρ' ρ'' σₖ'},
    lambda_huh v →
    Alloc (v, ρ, σᵥ, σₖ, a, t) b →
    Tick (v, ρ, σᵥ, σₖ, a, t) u →
    ks_lookup a σₖ (some (fn (lam x e) ρ' c)) →
    env_update x b ρ' ρ'' →
    ks_update b (fn v ρ a) σₖ σₖ' →
    Eval (v, ρ, σᵥ, σₖ, a, t)
         (e, ρ'', σᵥ, σₖ', b, u)

-- define the reflexive transitive closure of the small step semantics
inductive EvalReach : Σ → Σ → Prop where
  | refl : ∀ {s}, EvalReach s s
  | step : ∀ {s₁ s₂ s₃},
    EvalReach s₁ s₂ →
    EvalReach s₂ s₃ →
    EvalReach s₁ s₃

-- define halting state
-- halting state is we get a lambda expression and mt in the continuation store
inductive Halting : Σ → Prop where
  | halt : ∀ {v ρ σᵥ σₖ a t},
    lambda_huh v →
    ks_lookup a σₖ (some mt) →
    Halting (v, ρ, σᵥ, σₖ, a, t)


-- prove determinism for aeval
-- proof sketch:
-- induction on the derivation of aeval
-- case aeval_hit:
--   induction on the derivation of aeval
theorem aeval_determinism : ∀ {x e s v v'},
  aeval x e s v → aeval x e s v' → v = v' := by
  intros x e s v v' h₁ h₂
  induction h₁ generalizing v'
  case aeval_hit x a v e s h₁ h₂ =>

-- proof of determinism
-- theorem determinism_proof : determinism := by
--   intro s s₁ s₂ h₁ h₂
--   induction h₁ generalizing s₂
--   case eval_ref x ρ σ a t aeval₁ =>
--     cases h₂
--     .



-- prove progress of the small step semantics


end Lambda
