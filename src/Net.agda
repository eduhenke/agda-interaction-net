module Net where

open import Data.Nat using (ℕ; _<_; s≤s; z≤n; suc)
open import Data.Vec.Base using (Vec)
open import Data.String using (String)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Function.Bundles using (_↔_; Injection; Inverse; mk↔′)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; cong)

-- simpler isomorphism
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

record NodeContext : Set₁ where
  field
    T : Set
    P⁺ : T → ℕ
    P⁻ : T → ℕ

record Net {n : ℕ} (nc : NodeContext) : Set where
  T = NodeContext.T nc
  ncP⁺ = NodeContext.P⁺ nc
  ncP⁻ = NodeContext.P⁻ nc

  field
    -- we'll denote the set of nodes as Fin n
    -- as that gives us a finite set and a way to index one of the elements
    τ : Fin n → T
  
  -- a pair (n, m) such that n is a node and m is <= number of positive ports for this node
  -- (node 0, port⁺0), (node 0, port⁺1), ...
  P⁺ = Σ[ n ∈ Fin n ] Fin (ncP⁺ (τ n))
  P⁻ = Σ[ n ∈ Fin n ] Fin (ncP⁻ (τ n))

  field
    -- a way to connect each pair (n, m) of positive ports to their negative counterparts
    -- it is a bijection(isomorphism), because we can go from a positive port to a negative port and vice-versa
    w : P⁺ ≃ P⁻

data NodeType : Set where
  δ : NodeType
  ϵ : NodeType

Context₁ : NodeContext
Context₁ = record {
    T = NodeType
  ; P⁺ = λ{ δ → 2 ; ϵ → 0}
  ; P⁻ = λ{ δ → 0 ; ϵ → 1}
  }

-- ϵ₀
-- |
-- δ₁--ϵ₂

example₁ : Net {3} Context₁
example₁ = record {
    τ = λ{ 0F → ϵ ; 1F → δ ; 2F → ϵ}
  ; w = record {
      to = λ{ (1F , 0F) → 0F , 0F ; (1F , 1F) → 2F , 0F ; (1F , Fin.suc (Fin.suc ())) ; (2F , ()) ; (Fin.suc (Fin.suc (Fin.suc ())) , snd)}
    ; from = λ{ (0F , 0F) → 1F , 0F ; (2F , 0F) → 1F , 1F}
    ; from∘to = λ{ (1F , 0F) → refl ; (1F , 1F) → refl ; (2F , ()) ; (Fin.suc (Fin.suc (Fin.suc ())) , snd)}
    ; to∘from = λ{ (0F , 0F) → refl ; (2F , 0F) → refl}
    }
  }


Fin⁰ : ℕ → Set
Fin⁰ 0 = ⊥
Fin⁰ (suc n) = Σ[ f ∈ Fin (suc n) ] (f ≢ Fin.zero)

record Rule {on : ℕ} (nc : NodeContext) : Set where
  T = NodeContext.T nc
  ncP⁺ = NodeContext.P⁺ nc
  ncP⁻ = NodeContext.P⁻ nc

  field
    I⁺ I⁻ : T
  
  -- The set B+ := {n | 0 < n < P⁺(I⁺) } + {n ∈ N | n < P⁺(I⁻)} of positive boundary ports where + denotes a disjoint union.
  B⁺ = (Fin⁰ (ncP⁺ I⁺)) ⊎ Fin (ncP⁺ I⁻)
  -- The set B- := {n | 0 < n < P⁻(I⁻) } + {n ∈ N | n < P⁻(I⁺)} of negative boundary ports where + denotes a disjoint union.
  B⁻ = (Fin⁰ (ncP⁻ I⁻)) ⊎ Fin (ncP⁻ I⁺)

  field
    -- this function assigns a type to on nodes
    o : Fin on → T
    -- Fin on does not correlate directly to Fin n of the outer net
    -- convert : ∀ {n} → Fin on → Fin n
   
  O⁺ = Σ[ n ∈ Fin on ] Fin (ncP⁺ (o n))
  O⁻ = Σ[ n ∈ Fin on ] Fin (ncP⁻ (o n))
  
  field
    i : B⁻ ⊎ O⁺ ≃ B⁺ ⊎ O⁻

--   |
--   -
--   δ⁺+ ===    
--   +
--   |
--   -
--   δ⁻+ ===
--   +
--   |

-- Rule₁ : Rule {0} Context₁
-- Rule₁ = record {
--     I⁺ = δ
--   ; I⁻ = δ
--   ; o = λ{()}
-- --  ; convert = {!!}
--   ; i = record {
--       to = λ{
--         (inj₁ (inj₁ (0F , snd))) → inj₁ (inj₁ (1F , λ{()}))
--       ; (inj₁ (inj₂ 0F)) → inj₁ {!!}
--       }
--     ; from = {!!}
--     ; from∘to = {!!}
--     ; to∘from = {!!}
--     }
--   }
  
