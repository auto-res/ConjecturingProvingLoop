import Mathlib
import Aesop

namespace Topology

variable {X : Type*} [TopologicalSpace X]

/-- A set is semi-open if it is a subset of the closure of its interior. -/
def SemiOpen (A : Set X) : Prop :=
  A ⊆ closure (interior A)

/-- A set is alpha-open if it is a subset of the interior of the closure of its interior. -/
def AlphaOpen (A : Set X) : Prop :=
  A ⊆ interior (closure (interior A))

/-- A set is preopen if it is a subset of the interior of its closure. -/
def PreOpen (A : Set X) : Prop :=
  A ⊆ interior (closure A)


theorem alpha_open_implies_semi_open {A : Set X} (h : AlphaOpen A) : SemiOpen A := by
  exact h.trans (interior_subset : interior (closure (interior A)) ⊆ closure (interior A))

theorem compact_set_is_alpha_open_if_open {A : Set X} (h : IsCompact A) (ho : IsOpen A) : AlphaOpen A := by
  -- We must show `A ⊆ interior (closure (interior A))`.
  intro x hx
  -- Since `A` is open, its interior is itself.
  have hInt : interior A = A := ho.interior_eq
  -- We first prove that `x ∈ interior (closure A)`.
  have hx' : x ∈ interior (closure A) := by
    -- `A` is a neighbourhood of `x`.
    have hA_nhds : (A : Set X) ∈ 𝓝 x := ho.mem_nhds hx
    -- Therefore `closure A` is also a neighbourhood of `x`.
    have hCl_nhds : (closure A : Set X) ∈ 𝓝 x :=
      Filter.mem_of_superset hA_nhds subset_closure
    -- Hence `x` belongs to the interior of `closure A`.
    exact (mem_interior_iff_mem_nhds).2 hCl_nhds
  -- Re-express the goal using `interior A = A`.
  simpa [hInt] using hx'

theorem dense_set_is_preopen {A : Set X} (h : Dense A) : PreOpen A := by
  intro x hx
  simpa [h.closure_eq, interior_univ]

theorem preopen_closure_is_semi_open {A : Set X} (h : PreOpen A) : SemiOpen (closure A) := by
  exact closure_mono h

theorem union_of_preopen_closures_is_preopen {A B : Set X} (hA : PreOpen (closure A)) (hB : PreOpen (closure B)) : PreOpen (closure (A ∪ B)) := by
  -- Unfold the definition of `PreOpen`.
  intro x hx
  -- Rewrite the closure of the union as the union of the individual closures.
  have hx' : x ∈ closure A ∪ closure B := by
    simpa [closure_union] using hx
  -- Analyse the two possibilities.
  cases hx' with
  | inl hA_mem =>
      -- From `hA` we get that `x` is in the interior of `closure A`.
      have hA_int : x ∈ interior (closure A) := by
        have : x ∈ interior (closure (closure A)) := hA hA_mem
        simpa [closure_closure] using this
      -- `closure A` is contained in `closure A ∪ closure B`.
      have h_sub : (closure A : Set X) ⊆ closure A ∪ closure B := by
        intro y hy; exact Or.inl hy
      -- Hence the corresponding interiors are related.
      have h_in : x ∈ interior (closure A ∪ closure B) :=
        (interior_mono h_sub) hA_int
      -- Conclude the required membership after rewriting.
      simpa [closure_union, closure_closure] using h_in
  | inr hB_mem =>
      -- From `hB` we get that `x` is in the interior of `closure B`.
      have hB_int : x ∈ interior (closure B) := by
        have : x ∈ interior (closure (closure B)) := hB hB_mem
        simpa [closure_closure] using this
      -- `closure B` is contained in `closure A ∪ closure B`.
      have h_sub : (closure B : Set X) ⊆ closure A ∪ closure B := by
        intro y hy; exact Or.inr hy
      -- Hence the corresponding interiors are related.
      have h_in : x ∈ interior (closure A ∪ closure B) :=
        (interior_mono h_sub) hB_int
      -- Conclude the required membership after rewriting.
      simpa [closure_union, closure_closure] using h_in

theorem semi_open_union_dense_is_dense {A B : Set X} (hA : SemiOpen A) (hB : Dense B) : Dense (A ∪ B) := by
  -- First, `univ ⊆ closure (A ∪ B)` using the density of `B`.
  have h_univ_subset : (Set.univ : Set X) ⊆ closure (A ∪ B) := by
    -- Since `B ⊆ A ∪ B`, taking closures yields the required inclusion.
    have : (closure (B : Set X)) ⊆ closure (A ∪ B) := by
      exact closure_mono (by
        intro x hx
        exact Or.inr hx)
    -- Rewrite `closure B` using the density of `B`.
    simpa [hB.closure_eq] using this
  -- The converse inclusion is obvious.
  have h_subset_univ : closure (A ∪ B) ⊆ (Set.univ : Set X) := by
    intro x hx
    trivial
  -- Combine both inclusions into an equality of sets.
  have h_closure_eq : (closure (A ∪ B : Set X)) = Set.univ :=
    Set.Subset.antisymm h_subset_univ h_univ_subset
  -- Translate the closure equality into the desired density statement.
  simpa [Dense, h_closure_eq]

theorem preopen_interior_is_alpha_open {A : Set X} (hA : PreOpen A) : AlphaOpen (interior A) := by
  intro x hx
  -- `interior A` is an open neighbourhood of `x`.
  have h_nhds : (interior A : Set X) ∈ 𝓝 x :=
    IsOpen.mem_nhds isOpen_interior hx
  -- Hence its closure is also a neighbourhood of `x`.
  have h_cl : (closure (interior A) : Set X) ∈ 𝓝 x :=
    Filter.mem_of_superset h_nhds subset_closure
  -- Therefore `x` belongs to the interior of this closure.
  have h_mem : x ∈ interior (closure (interior A)) :=
    (mem_interior_iff_mem_nhds).2 h_cl
  -- Conclude using `interior_interior`.
  simpa [interior_interior] using h_mem

theorem dense_union_alpha_open_is_preopen {A B : Set X} (hA : Dense A) (hB : AlphaOpen B) : PreOpen (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      -- First, show `closure (A ∪ B) = univ`.
      have h_univ_subset : (Set.univ : Set X) ⊆ closure (A ∪ B) := by
        -- We know `closure A = univ` and `closure A ⊆ closure (A ∪ B)`.
        have : closure (A : Set X) ⊆ closure (A ∪ B) := by
          apply closure_mono
          intro y hy
          exact Or.inl hy
        simpa [hA.closure_eq] using this
      have h_closure_eq : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
        apply Set.Subset.antisymm
        · intro y hy; trivial
        · exact h_univ_subset
      -- Conclude that `x` is in the required interior.
      have : x ∈ (Set.univ : Set X) := by trivial
      simpa [h_closure_eq, interior_univ] using this
  | inr hxB =>
      -- `x ∈ B`
      -- Use the alpha-openness of `B`.
      have hB_int : x ∈ interior (closure (interior B)) := hB hxB
      -- Relate the closures.
      have h_sub : (closure (interior B : Set X)) ⊆ closure (A ∪ B) := by
        have h_sub0 : (interior B : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inr (interior_subset hy)
        exact closure_mono h_sub0
      -- Monotonicity of `interior` gives the result.
      exact (interior_mono h_sub) hB_int

theorem preopen_closure_of_dense_subset {A : Set X} (hA : Dense A) : PreOpen (closure A) := by
  intro x hx
  simpa [hA.closure_eq, interior_univ, closure_closure] using hx

theorem union_of_dense_sets_is_dense {A B : Set X} (hA : Dense A) (hB : Dense B) : Dense (A ∪ B) := by
  dsimp [Dense] at hA hB ⊢
  simp [closure_union, hA, hB]

theorem finite_union_of_preopen_sets_is_preopen {I : Type*} [Finite I] {f : I → Set X} (h : ∀ i, PreOpen (f i)) : PreOpen (⋃ i, f i) := by
  intro x hx
  -- Obtain an index `i` such that `x ∈ f i`.
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- Since `f i` is preopen, `x` belongs to `interior (closure (f i))`.
  have hx_int : x ∈ interior (closure (f i)) := h i hx_i
  -- `closure (f i)` is contained in `closure (⋃ j, f j)`.
  have h_subset : (closure (f i) : Set X) ⊆ closure (⋃ j, f j) := by
    -- First, `f i ⊆ ⋃ j, f j`.
    have h_sub' : (f i : Set X) ⊆ ⋃ j, f j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    -- Taking closures preserves inclusion.
    exact closure_mono h_sub'
  -- Monotonicity of `interior` yields the result.
  exact (interior_mono h_subset) hx_int

theorem open_set_is_alpha_open {A : Set X} (hA : IsOpen A) : AlphaOpen A := by
  intro x hx
  have h_nhds : (A : Set X) ∈ 𝓝 x := hA.mem_nhds hx
  have h_cl_nhds : (closure A : Set X) ∈ 𝓝 x :=
    Filter.mem_of_superset h_nhds subset_closure
  have : x ∈ interior (closure A) :=
    (mem_interior_iff_mem_nhds).2 h_cl_nhds
  simpa [hA.interior_eq] using this

theorem intersection_of_open_and_alpha_open_is_alpha_open {A B : Set X} (hA : IsOpen A) (hB : AlphaOpen B) : AlphaOpen (A ∩ B) := by
  -- We must prove `(A ∩ B) ⊆ interior (closure (interior (A ∩ B)))`.
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- `B` is α-open, hence:
  have hxBα : x ∈ interior (closure (interior B)) := hB hxB
  -- Consider the open neighbourhood  
  --   `S := A ∩ interior (closure (interior B))` of `x`.
  have hxS : x ∈ (A ∩ interior (closure (interior B))) := ⟨hxA, hxBα⟩
  have hS_open : IsOpen (A ∩ interior (closure (interior B))) :=
    hA.inter isOpen_interior
  ----------------------------------------------------------------
  -- We show `S ⊆ closure (interior (A ∩ B))`.
  ----------------------------------------------------------------
  have hS_subset :
      (A ∩ interior (closure (interior B)) : Set X) ⊆
        closure (interior (A ∩ B)) := by
    intro y hy
    rcases hy with ⟨hyA, hyIn⟩
    -- From `hyIn` we obtain `y ∈ closure (interior B)`.
    have hy_clIntB : y ∈ closure (interior B) :=
      (interior_subset : interior (closure (interior B)) ⊆ closure (interior B)) hyIn
    ----------------------------------------------------------------
    -- First: `y ∈ closure (A ∩ interior B)`.
    ----------------------------------------------------------------
    have hy_clAIntB : y ∈ closure (A ∩ interior B) := by
      -- Neighbourhood characterisation of closure.
      apply (mem_closure_iff).2
      intro U hU hyU
      -- `(U ∩ A)` is an open neighbourhood of `y`.
      have hUA_open : IsOpen (U ∩ A) := hU.inter hA
      have hy_UA   : y ∈ U ∩ A      := ⟨hyU, hyA⟩
      -- By `hy_clIntB`, this neighbourhood meets `interior B`.
      have h_nonempty : ((U ∩ A) ∩ interior B).Nonempty :=
        (mem_closure_iff).1 hy_clIntB _ hUA_open hy_UA
      -- Re-arrange the intersection.
      have : (U ∩ (A ∩ interior B)).Nonempty := by
        simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_right_comm] using h_nonempty
      simpa [Set.inter_assoc] using this
    ----------------------------------------------------------------
    -- Second: relate the two closures via `interior (A ∩ B)`.
    ----------------------------------------------------------------
    -- Because `A` is open we have `interior (A ∩ B) = A ∩ interior B`.
    have hInt_eq : interior (A ∩ B) = A ∩ interior B := by
      have : interior (A ∩ B) = interior A ∩ interior B := by
        simpa using interior_inter (A := A) (B := B)
      simpa [hA.interior_eq] using this
    -- Hence the desired membership.
    have : y ∈ closure (interior (A ∩ B)) := by
      -- rewrite RHS using `hInt_eq`
      simpa [hInt_eq] using hy_clAIntB
    exact this
  ----------------------------------------------------------------
  -- Maximality of interior supplies the inclusion we want.
  ----------------------------------------------------------------
  have hS_subset_int :
      (A ∩ interior (closure (interior B)) : Set X) ⊆
        interior (closure (interior (A ∩ B))) :=
    interior_maximal hS_subset hS_open
  exact hS_subset_int hxS

theorem preopen_of_closure_preopen {A : Set X} (h : PreOpen (closure A)) : PreOpen A := by
  intro x hx
  have hx_cl : x ∈ closure A := subset_closure hx
  have hx_int : x ∈ interior (closure (closure A)) := h hx_cl
  simpa [closure_closure] using hx_int

theorem closure_dense_implies_open {A : Set X} (hA : Dense A) : IsOpen (closure A) := by
  simpa [hA.closure_eq] using isOpen_univ

theorem semi_open_superset_closure {A : Set X} (hA : SemiOpen A) : closure A ⊆ closure (interior A) := by
  have h : closure A ⊆ closure (closure (interior A)) := closure_mono hA
  simpa [closure_closure] using h

theorem preopen_union_is_preopen_if_closure_is_preopen {A B : Set X} (hA : PreOpen (closure A)) (hB : PreOpen (closure B)) : PreOpen (A ∪ B) := by
  exact preopen_of_closure_preopen (union_of_preopen_closures_is_preopen hA hB)

theorem dense_inter_union_is_dense {A B : Set X} (hA : Dense A) (hB : Dense B) : Dense (A ∪ interior B) := by
  dsimp [Dense] at hA hB ⊢
  simp [closure_union, hA]

theorem interior_is_semi_open_in_compact_space {A : Set X} [h : CompactSpace X] : SemiOpen (interior A) := by
  dsimp [SemiOpen]
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem semi_open_interior_of_alpha_open {A : Set X} (hA : AlphaOpen A) : SemiOpen (interior A) := by
  dsimp [SemiOpen]
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem dense_alpha_open_union_semi_open_is_dense {A B : Set X} (hA : Dense A) (hB : SemiOpen B) : Dense (A ∪ B) := by
  simpa [Set.union_comm] using (semi_open_union_dense_is_dense hB hA)

theorem semi_open_interior_closure {A : Set X} : SemiOpen (interior (closure A)) := by
  dsimp [SemiOpen]
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem union_of_alpha_open_and_preopen_is_preopen {A B : Set X} (hA : AlphaOpen A) (hB : PreOpen B) : PreOpen (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA_mem =>
      -- `x ∈ A`
      have hA_int : x ∈ interior (closure (interior A)) := hA hA_mem
      -- `closure (interior A) ⊆ closure (A ∪ B)`
      have h_sub : (closure (interior A) : Set X) ⊆ closure (A ∪ B) := by
        -- first `closure (interior A) ⊆ closure A`
        have h1 : (closure (interior A) : Set X) ⊆ closure A :=
          closure_mono (interior_subset : (interior A : Set X) ⊆ A)
        -- then `closure A ⊆ closure (A ∪ B)`
        have h2 : (closure A : Set X) ⊆ closure (A ∪ B) :=
          closure_mono (by
            intro y hy
            exact Or.inl hy)
        exact Set.Subset.trans h1 h2
      -- conclude via monotonicity of `interior`
      exact (interior_mono h_sub) hA_int
  | inr hB_mem =>
      -- `x ∈ B`
      have hB_int : x ∈ interior (closure B) := hB hB_mem
      -- `closure B ⊆ closure (A ∪ B)`
      have h_sub : (closure (B : Set X)) ⊆ closure (A ∪ B) :=
        closure_mono (by
          intro y hy
          exact Or.inr hy)
      exact (interior_mono h_sub) hB_int

theorem dense_closure_is_alpha_open {A : Set X} (h : Dense A) : AlphaOpen (closure A) := by
  intro x hx
  simpa [h.closure_eq, interior_univ, closure_univ] using hx

theorem closure_semi_open_if_dense {A : Set X} (h : Dense A) : SemiOpen (closure A) := by
  dsimp [SemiOpen]
  intro x hx
  simpa [h.closure_eq, interior_univ, closure_univ] using hx

theorem semi_open_union_alpha_open_is_semi_open {A B : Set X} (hA : SemiOpen A) (hB : AlphaOpen B) : SemiOpen (A ∪ B) := by
  -- Unfold the definition of `SemiOpen`.
  dsimp [SemiOpen] at *
  intro x hx
  -- Analyse the two possibilities for `x`.
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      -- From the semi-openness of `A` we get:
      have hx_clA : x ∈ closure (interior A) := hA hxA
      -- Since `A ⊆ A ∪ B`, monotonicity of `interior` gives
      -- `interior A ⊆ interior (A ∪ B)`.
      have h_subset_int :
          (interior A : Set X) ⊆ interior (A ∪ B) := by
        have h_sub : (A : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact interior_mono h_sub
      -- Taking closures preserves inclusion.
      have h_subset_cl :
          (closure (interior A) : Set X) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_subset_int
      -- Conclude the required membership.
      exact h_subset_cl hx_clA
  | inr hxB =>
      -- `x ∈ B`
      -- From the α-openness of `B` we obtain semi-openness.
      have hB_semi : SemiOpen B := alpha_open_implies_semi_open hB
      have hx_clB : x ∈ closure (interior B) := hB_semi hxB
      -- As before, `B ⊆ A ∪ B` implies
      -- `interior B ⊆ interior (A ∪ B)`.
      have h_subset_int :
          (interior B : Set X) ⊆ interior (A ∪ B) := by
        have h_sub : (B : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inr hy
        exact interior_mono h_sub
      -- Taking closures preserves inclusion.
      have h_subset_cl :
          (closure (interior B) : Set X) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_subset_int
      -- Conclude the required membership.
      exact h_subset_cl hx_clB

theorem closure_is_preopen_in_discrete_space {A : Set X} [DiscreteTopology X] : PreOpen (closure A) := by
  -- Unfold the definition of `PreOpen`.
  dsimp [PreOpen]
  intro x hx
  -- In a discrete space every set is both closed and open.
  have h_closed : IsClosed (A : Set X) := isClosed_discrete _
  have h_open   : IsOpen   (A : Set X) := isOpen_discrete _
  -- Hence `closure A = A`.
  have h_closure_eq : (closure (A : Set X)) = A := h_closed.closure_eq
  -- Turn `hx : x ∈ closure A` into `x ∈ A`.
  have hxA : x ∈ A := by
    simpa [h_closure_eq] using hx
  -- Since `A` is open, its interior is itself, so `x ∈ interior A`.
  have hx_intA : x ∈ interior A := by
    simpa [h_open.interior_eq] using hxA
  -- Rewriting the goal using the equalities obtained above.
  simpa [closure_closure, h_closure_eq] using hx_intA

theorem alpha_open_interiors_of_closure {A : Set X} : AlphaOpen (interior (closure A)) := by
  simpa using
    (open_set_is_alpha_open (A := interior (closure (A : Set X))) isOpen_interior)

theorem preopen_if_discrete {A : Set X} [DiscreteTopology X] : PreOpen A := by
  dsimp [PreOpen]
  intro x hx
  have h_closed : IsClosed (A : Set X) := isClosed_discrete _
  have h_open : IsOpen (A : Set X) := isOpen_discrete _
  have h_closure_eq : (closure (A : Set X)) = A := h_closed.closure_eq
  have h_interior_eq : interior A = A := h_open.interior_eq
  simpa [h_closure_eq, h_interior_eq] using hx

theorem dense_union_with_open_is_dense {A B : Set X} (h₁ : Dense A) (h₂ : IsOpen B) : Dense (A ∪ B) := by
  dsimp [Dense] at h₁ ⊢
  simpa [closure_union, h₁]

theorem interior_of_alpha_open_is_preopen {A : Set X} (h : AlphaOpen A) : PreOpen (interior A) := by
  intro x hx
  exact h (interior_subset hx)

theorem open_intersection_semi_open_is_semi_open {A B : Set X} (hA : IsOpen A) (hB : SemiOpen B) : SemiOpen (A ∩ B) := by
  -- Unfold the definition of `SemiOpen`.
  dsimp [SemiOpen] at *
  intro x hx
  -- Split the membership information.
  rcases hx with ⟨hxA, hxB⟩
  -- From the semi–openness of `B` we have:
  have hx_closure_intB : x ∈ closure (interior B) := hB hxB
  -- We show that `x ∈ closure (interior (A ∩ B))` using
  -- the neighbourhood characterisation of the closure.
  apply (mem_closure_iff).2
  intro U hU hxU
  -- Consider the open neighbourhood `U ∩ A` of `x`.
  have hUA_open : IsOpen (U ∩ A) := hU.inter hA
  have hxUA     : x ∈ U ∩ A     := ⟨hxU, hxA⟩
  -- As `x` belongs to `closure (interior B)`, this neighbourhood
  -- meets `interior B`.
  have h_nonempty : ((U ∩ A) ∩ interior B).Nonempty := by
    have h_prop :=
      (mem_closure_iff).1 hx_closure_intB (U ∩ A) hUA_open hxUA
    simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_right_comm] using h_prop
  -- Extract a point witnessing the non-emptiness.
  rcases h_nonempty with ⟨y, ⟨hyU, hyA⟩, hyIntB⟩
  -- Because `A` is open, `interior (A ∩ B) = A ∩ interior B`.
  have h_int_eq : interior (A ∩ B) = A ∩ interior B := by
    have : interior (A ∩ B) = interior A ∩ interior B := by
      simpa using interior_inter (A := A) (B := B)
    simpa [hA.interior_eq] using this
  -- Hence `y` lies in `interior (A ∩ B)`.
  have hyInt : y ∈ interior (A ∩ B) := by
    have : y ∈ A ∩ interior B := ⟨hyA, hyIntB⟩
    simpa [h_int_eq] using this
  -- Finally, `y` is in the required intersection.
  exact ⟨y, ⟨hyU, hyInt⟩⟩

theorem compact_set_is_preopen_if_alpha_open {A : Set X} (h : IsCompact A) (hA : AlphaOpen A) : PreOpen A := by
  intro x hx
  -- `x` belongs to `interior (closure (interior A))` by α-openness.
  have h₁ : x ∈ interior (closure (interior A)) := hA hx
  -- Since `interior A ⊆ A`, we have `closure (interior A) ⊆ closure A`,
  -- hence, by monotonicity of `interior`, the following inclusion holds.
  have h₂ :
      (interior (closure (interior A)) : Set X) ⊆
        interior (closure A) :=
    interior_mono
      (closure_mono (interior_subset : (interior A : Set X) ⊆ A))
  -- The desired membership follows.
  exact h₂ h₁

theorem semi_open_closure_of_alpha_open {A : Set X} (h : AlphaOpen A) : SemiOpen (closure A) := by
  -- Unfold the definition of `SemiOpen`.
  dsimp [SemiOpen]
  -- We will show `closure A ⊆ closure (interior (closure A))`.
  intro x hx
  --------------------------------------------------------------------
  -- Step 1: we first prove `A ⊆ interior (closure A)`.
  --------------------------------------------------------------------
  have hA_int_closure : (A : Set X) ⊆ interior (closure A) := by
    -- `A ⊆ interior (closure (interior A))` by α-openness.
    -- We upgrade this to the desired inclusion using monotonicity.
    have h₁ : (closure (interior A) : Set X) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    have h₂ : (interior (closure (interior A)) : Set X) ⊆
        interior (closure A) :=
      interior_mono h₁
    intro y hy
    exact h₂ (h hy)
  --------------------------------------------------------------------
  -- Step 2: taking closures yields the required inclusion.
  --------------------------------------------------------------------
  have h_closure_incl :
      (closure A : Set X) ⊆ closure (interior (closure A)) :=
    closure_mono hA_int_closure
  --------------------------------------------------------------------
  -- Step 3: apply the inclusion to the point `x`.
  --------------------------------------------------------------------
  exact h_closure_incl hx

theorem union_preopen_is_dense_if_alpha_open_and_dense {A B : Set X} (hA : AlphaOpen A) (hB : Dense B) : Dense (A ∪ B) := by
  have hA' : SemiOpen A := alpha_open_implies_semi_open hA
  simpa using (semi_open_union_dense_is_dense hA' hB)

theorem intersection_of_semi_open_and_alpha_open_is_semi_open {A B : Set X} (hA : SemiOpen A) (hB : AlphaOpen B) : SemiOpen (A ∩ B) := by
  -- Unfold the definition of `SemiOpen`.
  dsimp [SemiOpen] at *
  -- Take an arbitrary point `x ∈ A ∩ B`.
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- From the semi-openness of `A` we have `x ∈ closure (interior A)`.
  have hA_cl : x ∈ closure (interior A) := hA hxA
  -- From the α-openness of `B` we have
  --   `x ∈ interior (closure (interior B))`.
  have hB_int : x ∈ interior (closure (interior B)) := hB hxB
  ------------------------------------------------------------------
  -- Goal: `x ∈ closure (interior (A ∩ B))`.
  -- We use the neighbourhood characterisation of the closure.
  ------------------------------------------------------------------
  apply (mem_closure_iff).2
  intro U hU hxU
  ------------------------------------------------------------------
  -- Step 1: intersect `U` with the open set
  --   `V := interior (closure (interior B))`.
  ------------------------------------------------------------------
  let V : Set X := interior (closure (interior B))
  have hV_open : IsOpen V := isOpen_interior
  have hxV : x ∈ V := by
    simpa [V] using hB_int
  -- `U₁ := U ∩ V` is an open neighbourhood of `x`.
  have hU₁_open : IsOpen (U ∩ V) := hU.inter hV_open
  have hxU₁ : x ∈ U ∩ V := ⟨hxU, hxV⟩
  ------------------------------------------------------------------
  -- Step 2: `hA_cl` guarantees that `U₁` meets `interior A`.
  ------------------------------------------------------------------
  have h_nonempty₁ :
      ((U ∩ V) ∩ interior A).Nonempty :=
    (mem_closure_iff).1 hA_cl (U ∩ V) hU₁_open hxU₁
  rcases h_nonempty₁ with ⟨y, ⟨hyUV, hyIntA⟩⟩
  have hyU  : y ∈ U := hyUV.1
  have hyV  : y ∈ V := hyUV.2
  ------------------------------------------------------------------
  -- Step 3: from `y ∈ V` we get `y ∈ closure (interior B)`.
  ------------------------------------------------------------------
  have hy_clB : y ∈ closure (interior B) := by
    -- `V ⊆ closure (interior B)`.
    have h_sub : (V : Set X) ⊆ closure (interior B) :=
      (interior_subset : (interior (closure (interior B)) : Set X) ⊆
        closure (interior B))
    exact h_sub hyV
  ------------------------------------------------------------------
  -- Step 4: use the previous fact to meet `interior B` while
  -- staying inside `U`.
  ------------------------------------------------------------------
  have hW_open : IsOpen (U ∩ interior A) := hU.inter isOpen_interior
  have hyW : y ∈ U ∩ interior A := ⟨hyU, hyIntA⟩
  have h_nonempty₂ :
      ((U ∩ interior A) ∩ interior B).Nonempty :=
    (mem_closure_iff).1 hy_clB (U ∩ interior A) hW_open hyW
  rcases h_nonempty₂ with ⟨z, ⟨hzW, hzIntB⟩⟩
  -- Now `z` lies in `U`, `interior A`, and `interior B`.
  have hzU     : z ∈ U := hzW.1
  have hzIntA  : z ∈ interior A := hzW.2
  ------------------------------------------------------------------
  -- Step 5: show `z ∈ interior (A ∩ B)`.
  ------------------------------------------------------------------
  have hzIntAB : z ∈ interior (A ∩ B) := by
    -- `interior A ∩ interior B` is open and contained in `A ∩ B`.
    have h_open : IsOpen (interior A ∩ interior B) :=
      isOpen_interior.inter isOpen_interior
    have h_subset :
        (interior A ∩ interior B : Set X) ⊆ (A ∩ B) := by
      intro t ht
      exact ⟨interior_subset ht.1, interior_subset ht.2⟩
    -- Hence, by maximality of the interior,
    --   `interior A ∩ interior B ⊆ interior (A ∩ B)`.
    have h_sub_int :
        (interior A ∩ interior B : Set X) ⊆ interior (A ∩ B) :=
      interior_maximal h_subset h_open
    -- Apply this inclusion to `z`.
    have hz_mem : z ∈ interior A ∩ interior B := ⟨hzIntA, hzIntB⟩
    exact h_sub_int hz_mem
  ------------------------------------------------------------------
  -- Step 6: provide the desired point in `U ∩ interior (A ∩ B)`.
  ------------------------------------------------------------------
  exact ⟨z, ⟨hzU, hzIntAB⟩⟩

theorem dense_and_semi_open_union_is_preopen {A B : Set X} (hA : Dense A) (hB : SemiOpen B) : PreOpen (A ∪ B) := by
  -- Unfold the definition of `PreOpen`.
  dsimp [PreOpen]
  intro x hx
  -- Because `A` is dense, its closure is the whole space.
  have h_closureA : (closure (A : Set X)) = (Set.univ : Set X) := hA.closure_eq
  -- Hence the closure of `A ∪ B` is also the whole space.
  have h_closure_union : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : (closure (A ∪ B : Set X)) = closure (A : Set X) ∪ closure (B : Set X) :=
      closure_union
    simpa [h_closureA, Set.univ_union] using this
  -- Trivially, any point belongs to `univ`.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  -- Rewriting gives the desired membership.
  simpa [h_closure_union, interior_univ] using this

theorem dense_inter_union_open_is_dense {A B : Set X} (hA : Dense A) (hB : IsOpen B) : Dense (A ∪ closure B) := by
  dsimp [Dense] at hA ⊢
  simpa [closure_union, closure_closure, hA, Set.univ_union]

theorem preopen_if_alpha_open_closure {A : Set X} (h : AlphaOpen (closure A)) : PreOpen A := by
  -- Unfold the definition of `PreOpen`.
  dsimp [PreOpen] at *
  intro x hxA
  -- Step 1: move the point from `A` to `closure A`.
  have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
  -- Step 2: use the α-openness of `closure A`.
  have hx_int :
      x ∈ interior (closure (interior (closure (A : Set X)))) :=
    h hx_cl
  -- Step 3: compare the two interiors that appear.
  have h_subset :
      (interior (closure (interior (closure (A : Set X)))) : Set X) ⊆
        interior (closure (A : Set X)) := by
    -- First show a relation between the corresponding closures.
    have h_closure_subset :
        (closure (interior (closure (A : Set X))) : Set X) ⊆
          closure (A : Set X) := by
      -- `interior (closure A) ⊆ closure A`
      -- ⇒ `closure (interior (closure A)) ⊆ closure (closure A)`
      -- and `closure (closure A)` is definitionally equal to `closure A`.
      have : (closure (interior (closure (A : Set X))) : Set X) ⊆
          closure (closure (A : Set X)) :=
        closure_mono
          (interior_subset :
            (interior (closure (A : Set X)) : Set X) ⊆ closure (A : Set X))
      simpa [closure_closure] using this
    -- Apply monotonicity of `interior`.
    exact interior_mono h_closure_subset
  -- Step 4: assemble the result.
  exact h_subset hx_int

theorem semi_open_interior_of_dense {A : Set X} (h : Dense A) : SemiOpen (interior A) := by
  dsimp [SemiOpen]
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem dense_union_is_preopen_if_semi_open {A B : Set X} (hA : SemiOpen A) (hB : Dense B) : PreOpen (A ∪ B) := by
  -- Unfold the definition of `PreOpen`.
  dsimp [PreOpen]
  intro x hx
  -- Since `B` is dense, `closure B = univ`.
  have h_closureB : (closure (B : Set X)) = (Set.univ : Set X) := hB.closure_eq
  -- Hence the closure of `A ∪ B` is also the whole space.
  have h_closure_union : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : (closure (A ∪ B : Set X)) = closure (A : Set X) ∪ closure (B : Set X) :=
      closure_union
    simpa [h_closureB, Set.union_univ] using this
  -- Trivially, any point belongs to `univ`.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  -- Rewriting gives the desired membership.
  simpa [h_closure_union, interior_univ] using this

theorem interior_of_preopen_is_semi_open {A : Set X} (h : PreOpen A) : SemiOpen (interior A) := by
  dsimp [SemiOpen]
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem closure_dense_union_of_alpha_open {A B : Set X} (hA : AlphaOpen A) (hB : Dense B) : Dense (closure (A ∪ B)) := by
  -- Expand `Dense` in hypothesis and goal.
  dsimp [Dense] at hB ⊢
  -- `closure B = univ`, hence `closure (A ∪ B) = univ`, and taking
  -- the closure once more does not change the set.
  simpa [closure_union, hB, Set.union_univ, closure_closure]

theorem open_union_alpha_open_is_preopen {A B : Set X} (hA : IsOpen A) (hB : AlphaOpen B) : PreOpen (A ∪ B) := by
  -- First, `A` being open implies it is preopen.
  have hA_pre : PreOpen A := by
    dsimp [PreOpen]
    intro x hx
    -- `A` is an open neighbourhood of `x`.
    have h_nhds : (A : Set X) ∈ 𝓝 x := hA.mem_nhds hx
    -- Therefore, its closure is also a neighbourhood of `x`.
    have h_cl_nhds : (closure A : Set X) ∈ 𝓝 x :=
      Filter.mem_of_superset h_nhds subset_closure
    -- Hence, `x` belongs to the interior of `closure A`.
    exact (mem_interior_iff_mem_nhds).2 h_cl_nhds
  -- Apply the lemma for the union of an α-open and a preopen set
  -- (with the roles of `A` and `B` swapped).
  have h_pre : PreOpen (B ∪ A) :=
    union_of_alpha_open_and_preopen_is_preopen hB hA_pre
  simpa [Set.union_comm] using h_pre

theorem alpha_open_inter_union_dense_is_preopen {A B : Set X} (hA : AlphaOpen A) (hB : Dense B) : PreOpen (A ∪ B) := by
  simpa [Set.union_comm] using (dense_union_alpha_open_is_preopen hB hA)

theorem finite_union_of_alpha_open_sets_is_alpha_open {I : Type*} [Finite I] {f : I → Set X} (h : ∀ i, AlphaOpen (f i)) : AlphaOpen (⋃ i, f i) := by
  -- Unfold `AlphaOpen`: we must show every `x` in the union
  -- belongs to `interior (closure (interior (⋃ i, f i)))`.
  intro x hx
  -- Pick the index witnessing `x`'s membership in the union.
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- From the α-openness of `f i` we obtain the required interior membership.
  have hx_int : x ∈ interior (closure (interior (f i))) := (h i) hx_i
  ------------------------------------------------------------------
  -- We now build an inclusion sending this interior to the desired one.
  ------------------------------------------------------------------
  have h_subset :
      (interior (closure (interior (f i))) : Set X) ⊆
        interior (closure (interior (⋃ j, f j))) := by
    -- First, compare the closures.
    have h_closure_subset :
        (closure (interior (f i)) : Set X) ⊆
          closure (interior (⋃ j, f j)) := by
      -- Step 1: `closure (interior (f i)) ⊆ closure (⋃ j, interior (f j))`.
      have h₁ :
          (closure (interior (f i)) : Set X) ⊆
            closure (⋃ j, interior (f j)) := by
        apply closure_mono
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      -- Step 2: `closure (⋃ j, interior (f j)) ⊆
      --          closure (interior (⋃ j, f j))`.
      have h₂ :
          (closure (⋃ j, interior (f j) : Set X)) ⊆
            closure (interior (⋃ j, f j)) := by
        -- `⋃ j, interior (f j)` is open and contained in `⋃ j, f j`.
        have h_union_subset :
            (⋃ j, interior (f j) : Set X) ⊆ interior (⋃ j, f j) := by
          -- It is open:
          have h_open : IsOpen (⋃ j, interior (f j)) := by
            apply isOpen_iUnion
            intro j
            exact isOpen_interior
          -- And clearly contained in the union:
          have h_sub : (⋃ j, interior (f j) : Set X) ⊆ (⋃ j, f j) := by
            intro y hy
            rcases Set.mem_iUnion.1 hy with ⟨j, hyj⟩
            exact Set.mem_iUnion.2 ⟨j, interior_subset hyj⟩
          -- Maximality of the interior gives the inclusion.
          exact interior_maximal h_sub h_open
        exact closure_mono h_union_subset
      -- Combine the two inclusions.
      exact Set.Subset.trans h₁ h₂
    -- Finally, apply monotonicity of `interior`.
    exact interior_mono h_closure_subset
  -- Apply the inclusion to finish.
  exact h_subset hx_int

theorem interior_of_union_is_alpha_open {A B : Set X} (hA : AlphaOpen A) (hB : AlphaOpen B) : AlphaOpen (interior (A ∪ B)) := by
  simpa using
    (open_set_is_alpha_open (A := interior (A ∪ B)) isOpen_interior)

theorem dense_preopen_union_is_dense {A B : Set X} (hA : PreOpen A) (hB : Dense B) : Dense (A ∪ B) := by
  dsimp [Dense] at hB ⊢
  simpa [closure_union, hB]

theorem intersection_of_preopen_and_open_is_preopen {A B : Set X} (hA : PreOpen A) (hB : IsOpen B) : PreOpen (A ∩ B) := by
  -- Unfold the definition of `PreOpen`.
  dsimp [PreOpen] at *
  -- Take a point `x ∈ A ∩ B`.
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- From the pre‐openness of `A` we get `x ∈ interior (closure A)`.
  have hxIntA : x ∈ interior (closure A) := hA hxA
  ------------------------------------------------------------------
  -- Consider the open neighbourhood `S := B ∩ interior (closure A)`
  -- of `x`.
  ------------------------------------------------------------------
  have hS_open : IsOpen (B ∩ interior (closure A)) :=
    hB.inter isOpen_interior
  have hxS : x ∈ (B ∩ interior (closure A)) := ⟨hxB, hxIntA⟩
  ------------------------------------------------------------------
  -- We show that `S ⊆ closure (A ∩ B)`.
  ------------------------------------------------------------------
  have hS_subset : (B ∩ interior (closure A) : Set X) ⊆ closure (A ∩ B) := by
    intro y hyS
    rcases hyS with ⟨hyB, hyIntA⟩
    -- `y ∈ closure A`.
    have hy_clA : y ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hyIntA
    ----------------------------------------------------------------
    -- Prove `y ∈ closure (A ∩ B)` using the neighbourhood
    -- characterisation of the closure.
    ----------------------------------------------------------------
    have : y ∈ closure (A ∩ B) := by
      -- Use `mem_closure_iff`.
      apply (mem_closure_iff).2
      intro V hV hyV
      -- Work with the open neighbourhood `V ∩ B` of `y`.
      have hV'open : IsOpen (V ∩ B) := hV.inter hB
      have hyV' : y ∈ V ∩ B := ⟨hyV, hyB⟩
      -- Since `y ∈ closure A`, this neighbourhood meets `A`.
      have h_nonempty : ((V ∩ B) ∩ A).Nonempty :=
        (mem_closure_iff).1 hy_clA (V ∩ B) hV'open hyV'
      -- Extract a witness `z`.
      rcases h_nonempty with ⟨z, ⟨⟨hzV, hzB⟩, hzA⟩⟩
      -- `z` lies in `V ∩ (A ∩ B)`, as required.
      exact ⟨z, ⟨hzV, ⟨hzA, hzB⟩⟩⟩
    exact this
  ------------------------------------------------------------------
  -- Maximality of the interior gives the desired inclusion.
  ------------------------------------------------------------------
  have hS_subset_int :
      (B ∩ interior (closure A) : Set X) ⊆ interior (closure (A ∩ B)) :=
    interior_maximal hS_subset hS_open
  -- Apply this inclusion to `x`.
  exact hS_subset_int hxS

theorem intersection_of_alpha_open_sets_is_alpha_open {A B : Set X} (hA : AlphaOpen A) (hB : AlphaOpen B) : AlphaOpen (A ∩ B) := by
  -- We unfold the definition of `AlphaOpen` and start with a point
  -- `x ∈ A ∩ B`.
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- From the α–openness of `A` and `B` we obtain the two interior
  -- memberships below.
  have hA_int : x ∈ interior (closure (interior A)) := hA hxA
  have hB_int : x ∈ interior (closure (interior B)) := hB hxB
  ------------------------------------------------------------------
  -- Consider the open neighbourhood
  --   `U := interior (closure (interior A))
  --         ∩ interior (closure (interior B))` of `x`.
  ------------------------------------------------------------------
  have hU_open :
      IsOpen (interior (closure (interior A)) ∩
              interior (closure (interior B))) :=
    isOpen_interior.inter isOpen_interior
  have hxU :
      x ∈ interior (closure (interior A)) ∩
          interior (closure (interior B)) := ⟨hA_int, hB_int⟩
  ------------------------------------------------------------------
  -- We prove that `U ⊆ closure (interior (A ∩ B))`.
  ------------------------------------------------------------------
  have hU_subset :
      (interior (closure (interior A)) ∩
        interior (closure (interior B)) : Set X) ⊆
        closure (interior (A ∩ B)) := by
    intro y hyU
    rcases hyU with ⟨hyA_int, hyB_int⟩
    -- From `hyA_int` and `hyB_int` we obtain the two closure
    -- memberships below.
    have hyA_cl : y ∈ closure (interior A) :=
      (interior_subset :
          interior (closure (interior A)) ⊆ closure (interior A)) hyA_int
    have hyB_cl : y ∈ closure (interior B) :=
      (interior_subset :
          interior (closure (interior B)) ⊆ closure (interior B)) hyB_int
    ----------------------------------------------------------------
    -- To show `y ∈ closure (interior (A ∩ B))`
    -- we use the neighbourhood characterisation of the closure.
    ----------------------------------------------------------------
    apply (mem_closure_iff).2
    intro V hV hyV
    --------------------------------------------------------------
    -- First step: work inside
    --   `V₁ := V ∩ interior (closure (interior B))`.
    --------------------------------------------------------------
    have hV₁_open :
        IsOpen (V ∩ interior (closure (interior B))) :=
      hV.inter isOpen_interior
    have hyV₁ : y ∈ V ∩ interior (closure (interior B)) :=
      ⟨hyV, hyB_int⟩
    -- As `y ∈ closure (interior A)`, this neighbourhood meets
    -- `interior A`.
    have h_nonempty₁ :
        ((V ∩ interior (closure (interior B))) ∩ interior A).Nonempty :=
      (mem_closure_iff).1 hyA_cl _ hV₁_open hyV₁
    rcases h_nonempty₁ with
      ⟨y₁, ⟨⟨hy₁V, hy₁B_int⟩, hy₁IntA⟩⟩
    --------------------------------------------------------------
    -- Now `y₁ ∈ V ∩ interior A` **and**
    -- `y₁ ∈ interior (closure (interior B))`.
    -- Hence `y₁ ∈ closure (interior B)`.
    --------------------------------------------------------------
    have hy₁_clB : y₁ ∈ closure (interior B) :=
      (interior_subset :
          interior (closure (interior B)) ⊆ closure (interior B)) hy₁B_int
    --------------------------------------------------------------
    -- Second step: work inside
    --   `V₂ := V ∩ interior A`.
    --------------------------------------------------------------
    have hV₂_open : IsOpen (V ∩ interior A) :=
      hV.inter isOpen_interior
    have hy₁V₂ : y₁ ∈ V ∩ interior A := ⟨hy₁V, hy₁IntA⟩
    -- Because `y₁ ∈ closure (interior B)`, the set `V₂` meets
    -- `interior B`.
    have h_nonempty₂ :
        ((V ∩ interior A) ∩ interior B).Nonempty :=
      (mem_closure_iff).1 hy₁_clB _ hV₂_open hy₁V₂
    rcases h_nonempty₂ with
      ⟨z, ⟨⟨hzV, hzIntA⟩, hzIntB⟩⟩
    --------------------------------------------------------------
    -- The point `z` lies in `V`, `interior A`, and `interior B`;
    -- hence it belongs to `interior (A ∩ B)`.
    --------------------------------------------------------------
    have hzIntAB : z ∈ interior (A ∩ B) := by
      -- Use maximality of the interior to pass from
      -- `interior A ∩ interior B` to `interior (A ∩ B)`.
      have h_sub :
          (interior A ∩ interior B : Set X) ⊆ interior (A ∩ B) :=
        interior_maximal
          (by
            intro t ht
            rcases ht with ⟨htA, htB⟩
            exact And.intro (interior_subset htA) (interior_subset htB))
          (isOpen_interior.inter isOpen_interior)
      exact h_sub ⟨hzIntA, hzIntB⟩
    -- We have found a point in `V ∩ interior (A ∩ B)`.
    exact ⟨z, ⟨hzV, hzIntAB⟩⟩
  ------------------------------------------------------------------
  -- Maximality of the interior gives the desired inclusion,
  -- and we conclude with the membership of `x` in `U`.
  ------------------------------------------------------------------
  have hU_subset_int :
      (interior (closure (interior A)) ∩
        interior (closure (interior B)) : Set X) ⊆
          interior (closure (interior (A ∩ B))) :=
    interior_maximal hU_subset hU_open
  exact hU_subset_int hxU

theorem finite_intersection_of_alpha_open_sets_is_alpha_open {I : Type*} [Finite I] {f : I → Set X} (h : ∀ i, AlphaOpen (f i)) : AlphaOpen (⋂ i, f i) := by
  classical
  -- `Finset` utilities need decidable equality and a `Fintype` instance.
  haveI := Classical.decEq I
  haveI := (Fintype.ofFinite I)
  -- The intersection of the sets `f i` over a finset `s`.
  let InterFinset : Finset I → Set X :=
    fun s => {x | ∀ i : I, (i : I) ∈ s → x ∈ f i}
  ------------------------------------------------------------------
  -- Step 1: prove by induction on a finset that this intersection
  -- is α-open.
  ------------------------------------------------------------------
  have hInter : ∀ s : Finset I, AlphaOpen (InterFinset s) := by
    intro s
    refine s.induction ?h0 ?hstep
    · -- Base case: `s = ∅`, the intersection is `univ`.
      have h_eq : InterFinset (∅ : Finset I) = (Set.univ : Set X) := by
        ext x
        simp [InterFinset]
      simpa [h_eq] using
        (open_set_is_alpha_open (A := (Set.univ : Set X)) isOpen_univ)
    · -- Inductive step: `s = insert a t`, with `a ∉ t`.
      intro a t ha_notmem ih
      -- Express the intersection as a binary intersection.
      have h_eq :
          InterFinset (insert a t) = (f a ∩ InterFinset t) := by
        ext x
        constructor
        · intro hx
          have hfa : x ∈ f a := hx a (by simp)
          have hft : x ∈ InterFinset t := by
            dsimp [InterFinset] at *
            intro i hi
            have hmem : (i : I) ∈ insert a t :=
              (Finset.mem_insert.mpr (Or.inr hi))
            exact hx i hmem
          exact ⟨hfa, hft⟩
        · intro hx
          rcases hx with ⟨hfa, hft⟩
          dsimp [InterFinset] at hft ⊢
          intro i hi
          have hi' : i = a ∨ i ∈ t := (Finset.mem_insert).1 hi
          cases hi' with
          | inl h_eqi => simpa [h_eqi] using hfa
          | inr h_in_t => exact hft i h_in_t
      -- Apply the two-set intersection lemma.
      have h_alpha : AlphaOpen (f a ∩ InterFinset t) :=
        intersection_of_alpha_open_sets_is_alpha_open (h a) ih
      simpa [h_eq] using h_alpha
  ------------------------------------------------------------------
  -- Step 2: apply the result to `Finset.univ`, i.e. all indices.
  ------------------------------------------------------------------
  have h_univ : AlphaOpen (InterFinset (Finset.univ : Finset I)) :=
    hInter (Finset.univ)
  ------------------------------------------------------------------
  -- Step 3: relate this set to the unrestricted intersection.
  ------------------------------------------------------------------
  have h_eq : (⋂ i, f i) = InterFinset (Finset.univ : Finset I) := by
    ext x
    constructor
    · intro hx
      dsimp [InterFinset]
      exact fun i _ => (Set.mem_iInter.1 hx) i
    · intro hx
      have : ∀ i : I, x ∈ f i := by
        intro i
        have hi : (i : I) ∈ (Finset.univ : Finset I) := by simp
        exact hx i hi
      exact (Set.mem_iInter.2 this)
  ------------------------------------------------------------------
  -- Step 4: conclude for the desired (infinite) intersection.
  ------------------------------------------------------------------
  simpa [h_eq] using h_univ

theorem union_of_semi_open_closure_and_dense_is_dense {A B : Set X} (hA : SemiOpen (closure A)) (hB : Dense B) : Dense (A ∪ B) := by
  dsimp [Dense] at hB ⊢
  simpa [closure_union, hB, Set.union_univ]

theorem semi_open_intersection_with_alpha_open {A B : Set X} (hA : SemiOpen A) (hB : AlphaOpen B) : SemiOpen (A ∩ interior B) := by
  -- Unfold the definition of `SemiOpen`.
  dsimp [SemiOpen] at *
  -- Take a point `x ∈ A ∩ interior B`.
  intro x hx
  rcases hx with ⟨hxA, hxIntB⟩
  -- From the semi–openness of `A` we have `x ∈ closure (interior A)`.
  have hx_closure_intA : x ∈ closure (interior A) := hA hxA
  ------------------------------------------------------------------
  -- Goal: `x ∈ closure (interior (A ∩ interior B))`.
  -- We use the neighbourhood characterisation of the closure.
  ------------------------------------------------------------------
  apply (mem_closure_iff).2
  intro U hU hxU
  ------------------------------------------------------------------
  -- Step 1: work inside the open neighbourhood
  --   `U₁ := U ∩ interior B` of `x`.
  ------------------------------------------------------------------
  have hU₁_open : IsOpen (U ∩ interior B) := hU.inter isOpen_interior
  have hxU₁ : x ∈ U ∩ interior B := ⟨hxU, hxIntB⟩
  -- As `x ∈ closure (interior A)`, this neighbourhood meets `interior A`.
  have h_nonempty₁ :
      ((U ∩ interior B) ∩ interior A).Nonempty :=
    (mem_closure_iff).1 hx_closure_intA _ hU₁_open hxU₁
  rcases h_nonempty₁ with ⟨y, ⟨⟨hyU, hyIntB⟩, hyIntA⟩⟩
  ------------------------------------------------------------------
  -- Step 2: `y` lies in `interior A ∩ interior B`.
  ------------------------------------------------------------------
  have hyIntAB : y ∈ interior A ∩ interior B := ⟨hyIntA, hyIntB⟩
  ------------------------------------------------------------------
  -- Step 3: `interior A ∩ interior B ⊆ interior (A ∩ interior B)`.
  ------------------------------------------------------------------
  have h_subset :
      (interior A ∩ interior B : Set X) ⊆ interior (A ∩ interior B) := by
    -- The set on the left is open and contained in `A ∩ interior B`.
    have h_open : IsOpen (interior A ∩ interior B) :=
      isOpen_interior.inter isOpen_interior
    have h_ss : (interior A ∩ interior B : Set X) ⊆ (A ∩ interior B) := by
      intro z hz
      exact ⟨interior_subset hz.1, hz.2⟩
    -- Apply maximality of the interior.
    exact interior_maximal h_ss h_open
  have hy_goal : y ∈ interior (A ∩ interior B) := h_subset hyIntAB
  ------------------------------------------------------------------
  -- Step 4: furnish the required witness in `U ∩ interior (A ∩ interior B)`.
  ------------------------------------------------------------------
  exact ⟨y, ⟨hyU, hy_goal⟩⟩

theorem preopen_intersection_of_alpha_open {A B : Set X} (hA : AlphaOpen A) (hB : PreOpen B) : PreOpen (A ∩ B) := by
  -- Unfold the definition of `PreOpen`.
  dsimp [PreOpen] at *
  -- Take a point `x ∈ A ∩ B`.
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- From the α–openness of `A` we have
  have hA_int : x ∈ interior (closure (interior A)) := hA hxA
  -- From the pre–openness of `B` we have
  have hB_int : x ∈ interior (closure B) := hB hxB
  --------------------------------------------------------------------
  -- Consider the open neighbourhood
  --   `U := interior (closure (interior A)) ∩ interior (closure B)`
  -- of `x`.
  --------------------------------------------------------------------
  have hU_open :
      IsOpen (interior (closure (interior A)) ∩ interior (closure B)) :=
    isOpen_interior.inter isOpen_interior
  have hxU :
      x ∈ interior (closure (interior A)) ∩ interior (closure B) :=
    ⟨hA_int, hB_int⟩
  --------------------------------------------------------------------
  -- We show `U ⊆ closure (A ∩ B)`.
  --------------------------------------------------------------------
  have hU_subset :
      (interior (closure (interior A)) ∩ interior (closure B) : Set X) ⊆
        closure (A ∩ B) := by
    intro y hyU
    rcases hyU with ⟨hyA_int, hyB_int⟩
    -- `y` lies in the two closures below.
    have hy_clB : y ∈ closure B :=
      (interior_subset : interior (closure B) ⊆ closure B) hyB_int
    have hy_clIntA : y ∈ closure (interior A) :=
      (interior_subset :
          interior (closure (interior A)) ⊆ closure (interior A)) hyA_int
    ----------------------------------------------------------------
    -- Neighbourhood characterisation of the closure.
    ----------------------------------------------------------------
    apply (mem_closure_iff).2
    intro V hV hyV
    --------------------------------------------------------------
    -- First step: work in `V₁ := V ∩ interior (closure B)`.
    --------------------------------------------------------------
    have hV₁_open : IsOpen (V ∩ interior (closure B)) :=
      hV.inter isOpen_interior
    have hyV₁ : y ∈ V ∩ interior (closure B) := ⟨hyV, hyB_int⟩
    -- This neighbourhood meets `interior A`.
    have h_nonempty₁ :
        ((V ∩ interior (closure B)) ∩ interior A).Nonempty :=
      (mem_closure_iff).1 hy_clIntA _ hV₁_open hyV₁
    rcases h_nonempty₁ with
      ⟨y₁, ⟨⟨hy₁V, hy₁IntClB⟩, hy₁IntA⟩⟩
    --------------------------------------------------------------
    -- Now `y₁ ∈ closure B`.
    --------------------------------------------------------------
    have hy₁_clB : y₁ ∈ closure B :=
      (interior_subset :
          interior (closure B) ⊆ closure B) hy₁IntClB
    --------------------------------------------------------------
    -- Second step: work in `V₂ := V ∩ interior A`.
    --------------------------------------------------------------
    have hV₂_open : IsOpen (V ∩ interior A) :=
      hV.inter isOpen_interior
    have hy₁V₂ : y₁ ∈ V ∩ interior A := ⟨hy₁V, hy₁IntA⟩
    -- This neighbourhood meets `B`.
    have h_nonempty₂ :
        ((V ∩ interior A) ∩ B).Nonempty :=
      (mem_closure_iff).1 hy₁_clB _ hV₂_open hy₁V₂
    rcases h_nonempty₂ with
      ⟨z, ⟨⟨hzV, hzIntA⟩, hzB⟩⟩
    -- `z` lies in `A` because it is in `interior A`.
    have hzA : z ∈ A := interior_subset hzIntA
    -- Hence `z ∈ V ∩ (A ∩ B)`.
    exact ⟨z, ⟨hzV, ⟨hzA, hzB⟩⟩⟩
  --------------------------------------------------------------------
  -- Maximality of the interior gives the desired inclusion.
  --------------------------------------------------------------------
  have hU_subset_int :
      (interior (closure (interior A)) ∩ interior (closure B) : Set X) ⊆
        interior (closure (A ∩ B)) :=
    interior_maximal hU_subset hU_open
  -- Apply this inclusion to `x`.
  exact hU_subset_int hxU

theorem semi_open_closure_intersection_with_alpha_open {A B : Set X} (hA : SemiOpen A) (hB : AlphaOpen B) : SemiOpen (closure (A ∩ B)) := by
  -- First, `A ∩ B` is semi-open.
  have hAB : SemiOpen (A ∩ B) :=
    intersection_of_semi_open_and_alpha_open_is_semi_open hA hB
  -- Unfold the definition of `SemiOpen` everywhere.
  dsimp [SemiOpen] at hAB ⊢
  -- Take `x ∈ closure (A ∩ B)`.
  intro x hx
  ------------------------------------------------------------------
  -- Step 1.  From the semi-openness of `A ∩ B` we move `x`
  --          into `closure (interior (A ∩ B))`.
  ------------------------------------------------------------------
  have h₁ : x ∈ closure (interior (A ∩ B)) := by
    -- `hAB : A ∩ B ⊆ closure (interior (A ∩ B))`.
    -- Taking closures gives
    --   `closure (A ∩ B) ⊆ closure (closure (interior (A ∩ B)))`.
    have hsub :
        (closure (A ∩ B) : Set X) ⊆
          closure (closure (interior (A ∩ B))) :=
      closure_mono hAB
    -- Apply this inclusion to `hx`.
    have : x ∈ closure (closure (interior (A ∩ B))) := hsub hx
    -- Remove the redundant closure.
    simpa [closure_closure] using this
  ------------------------------------------------------------------
  -- Step 2.  Compare the two interiors.
  ------------------------------------------------------------------
  have h₂ :
      (closure (interior (A ∩ B)) : Set X) ⊆
        closure (interior (closure (A ∩ B))) := by
    -- Because `A ∩ B ⊆ closure (A ∩ B)` we have
    -- `interior (A ∩ B) ⊆ interior (closure (A ∩ B))`.
    have h_int :
        (interior (A ∩ B) : Set X) ⊆ interior (closure (A ∩ B)) :=
      interior_mono
        (subset_closure : (A ∩ B : Set X) ⊆ closure (A ∩ B))
    -- Taking closures preserves inclusion.
    exact closure_mono h_int
  ------------------------------------------------------------------
  -- Step 3.  Assemble the result.
  ------------------------------------------------------------------
  exact h₂ h₁

theorem alpha_open_iff_union_with_dense_is_preopen {A B : Set X} (hA : AlphaOpen A) (hB : Dense B) : PreOpen (closure (A ∪ B)) ↔ AlphaOpen A := by
  constructor
  · intro _hPre
    exact hA
  · intro _hAlpha
    -- First identify the closure of `A ∪ B`.
    have h_closure_union :
        (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
      have : closure (A ∪ B : Set X) =
          closure (A : Set X) ∪ closure (B : Set X) := by
        simpa using (closure_union (A := A) (B := B))
      simpa [hB.closure_eq, Set.union_univ] using this
    -- It therefore suffices to show that `univ` is preopen.
    have h_pre_univ : PreOpen (Set.univ : Set X) := by
      dsimp [PreOpen]
      intro x hx
      simpa [closure_univ, interior_univ] using hx
    simpa [h_closure_union] using h_pre_univ

theorem intersection_with_open_is_semi_open {A B : Set X} (hA : SemiOpen A) (hB : IsOpen B) : SemiOpen (A ∩ B) := by
  simpa [Set.inter_comm] using
    (open_intersection_semi_open_is_semi_open hB hA)

theorem finite_union_of_semi_open_sets_is_semi_open {I : Type*} [Finite I] {f : I → Set X} (h : ∀ i, SemiOpen (f i)) : SemiOpen (⋃ i, f i) := by
  -- Unfold `SemiOpen` in the hypotheses.
  dsimp [SemiOpen] at h
  -- Unfold `SemiOpen` in the goal and introduce a point `x`.
  intro x hx
  -- `x` lies in one of the `f i`.
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- Use the semi–openness of `f i`.
  have hx_cl : x ∈ closure (interior (f i)) := (h i) hx_i
  -- Relate the two closures that appear.
  have h_subset :
      (closure (interior (f i)) : Set X) ⊆
        closure (interior (⋃ j, f j)) := by
    -- First, relate the corresponding interiors.
    have h_int :
        (interior (f i) : Set X) ⊆ interior (⋃ j, f j) := by
      -- Since `f i ⊆ ⋃ j, f j`, apply `interior_mono`.
      have h_sub : (f i : Set X) ⊆ ⋃ j, f j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_sub
    -- Taking closures preserves inclusion.
    exact closure_mono h_int
  -- Conclude.
  exact h_subset hx_cl

theorem closure_of_semi_open_union_alpha_open {A B : Set X} (hA : SemiOpen A) (hB : AlphaOpen B) : SemiOpen (closure (A ∪ B)) := by
  -- We unfold the definition of `SemiOpen` for the hypothesis and the goal.
  dsimp [SemiOpen] at hA ⊢
  -- We want to prove:
  --   `closure (A ∪ B) ⊆ closure (interior (closure (A ∪ B)))`.
  -- A convenient way is to first show the inclusion for `A ∪ B`
  -- itself and then use `closure_minimal`.
  have h_sub :
      (A ∪ B : Set X) ⊆ closure (interior (closure (A ∪ B))) := by
    intro y hy
    -- Split according to whether `y ∈ A` or `y ∈ B`.
    cases hy with
    | inl hyA =>
        -- `y ∈ A`
        -- From the semi–openness of `A` we have
        --   `y ∈ closure (interior A)`.
        have hy_clIntA : y ∈ closure (interior A) := hA hyA
        -- We show that `closure (interior A)` is contained
        -- in `closure (interior (closure (A ∪ B)))`.
        have h_incl :
            (closure (interior A) : Set X) ⊆
              closure (interior (closure (A ∪ B))) := by
          -- First, `interior A ⊆ interior (closure (A ∪ B))`.
          have h_int :
              (interior A : Set X) ⊆ interior (closure (A ∪ B)) := by
            -- Because `A ⊆ closure (A ∪ B)`.
            have hA_sub : (A : Set X) ⊆ closure (A ∪ B) := by
              intro z hz
              have : (z ∈ A ∪ B) := Or.inl hz
              exact subset_closure this
            exact interior_mono hA_sub
          -- Taking closures preserves inclusion.
          exact closure_mono h_int
        exact h_incl hy_clIntA
    | inr hyB =>
        -- `y ∈ B`
        -- From the α–openness of `B` we obtain
        --   `y ∈ interior (closure (interior B))`.
        have hy_int : y ∈ interior (closure (interior B)) := hB hyB
        -- We move along the chain
        --   interior (closure (interior B))
        --     ⊆ closure (interior B)
        --     ⊆ closure (interior (closure (A ∪ B))).
        have h_chain :
            (interior (closure (interior B)) : Set X) ⊆
              closure (interior (closure (A ∪ B))) := by
          -- First link: `interior (closure (interior B)) ⊆ closure (interior B)`.
          have h₁ :
              (interior (closure (interior B)) : Set X) ⊆
                closure (interior B) :=
            interior_subset
          -- Second link:
          --   `closure (interior B) ⊆ closure (interior (closure (A ∪ B)))`.
          have h₂ :
              (closure (interior B) : Set X) ⊆
                closure (interior (closure (A ∪ B))) := by
            -- Start with `interior B ⊆ interior (closure (A ∪ B))`.
            have h_intB_sub :
                (interior B : Set X) ⊆ interior (closure (A ∪ B)) := by
              -- Because `B ⊆ closure (A ∪ B)`.
              have hB_sub : (B : Set X) ⊆ closure (A ∪ B) := by
                intro z hz
                have : (z ∈ A ∪ B) := Or.inr hz
                exact subset_closure this
              exact interior_mono hB_sub
            -- Taking closures gives the desired inclusion.
            exact closure_mono h_intB_sub
          -- Combine the two links.
          exact Set.Subset.trans h₁ h₂
        exact h_chain hy_int
  -- `closure (interior (closure (A ∪ B)))` is a closed set.
  have h_closed : IsClosed (closure (interior (closure (A ∪ B)))) :=
    isClosed_closure
  -- By `closure_minimal`, the closure of `A ∪ B` is contained in it.
  have h_closure_sub :
      (closure (A ∪ B : Set X)) ⊆
        closure (interior (closure (A ∪ B))) :=
    closure_minimal h_sub h_closed
  -- Apply the inclusion to the point provided by the goal.
  exact h_closure_sub

theorem alpha_open_interior_intersection_of_preopen {A B : Set X} (hA : PreOpen A) (hB : PreOpen B) : AlphaOpen (interior (A ∩ B)) := by
  simpa using
    (open_set_is_alpha_open (A := interior (A ∩ B)) isOpen_interior)

theorem intersection_with_alpha_open_in_discrete_space {A : Set X} [DiscreteTopology X] (hA : AlphaOpen A) : AlphaOpen (A ∩ Set.univ) := by
  simpa [Set.inter_univ] using hA

theorem closure_of_dense_union_is_dense {A B : Set X} (hA : Dense A) (hB : Dense B) : Dense (closure (A ∪ B)) := by
  dsimp [Dense] at hA hB ⊢
  simpa [closure_closure, closure_union, hA, hB]

theorem dense_preopen_union_are_preopen {A B : Set X} (hA : Dense A) (hB : PreOpen B) : PreOpen (A ∪ B) := by
  -- Unfold the definition of `PreOpen`.
  dsimp [PreOpen] at *
  intro x hx
  -- Because `A` is dense, its closure is the whole space.
  have h_closureA : (closure (A : Set X)) = (Set.univ : Set X) := hA.closure_eq
  -- Hence the closure of `A ∪ B` is also the whole space.
  have h_closure_union : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : closure (A ∪ B : Set X) =
        closure (A : Set X) ∪ closure (B : Set X) :=
      closure_union
    simpa [h_closureA, Set.univ_union] using this
  -- Trivially, any point belongs to `univ`.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  -- Rewriting gives the desired membership.
  simpa [h_closure_union, interior_univ] using this

theorem interior_closure_of_dense_is_dense {A : Set X} (h : Dense A) : Dense (interior (closure A)) := by
  -- First, translate the density of `A` into the statement
  -- `closure A = univ`.
  have h_closure : (closure (A : Set X)) = (Set.univ : Set X) := h.closure_eq
  -- Unfold `Dense` in the goal.
  dsimp [Dense]
  intro x
  -- Rewrite using `h_closure` and finish with `simp`.
  simp [h_closure, interior_univ, closure_univ]

theorem semi_open_intersections_alpha_open {A B : Set X} (hA : SemiOpen A) (hB : AlphaOpen B) : SemiOpen (interior (A ∩ B)) := by
  dsimp [SemiOpen]
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem interior_preopen_union_is_alpha_open {A B : Set X} (hA : PreOpen A) (hB : AlphaOpen B) : AlphaOpen (interior (A ∪ B)) := by
  simpa using
    (open_set_is_alpha_open (A := interior (A ∪ B)) isOpen_interior)

theorem closure_semi_open {A : Set X} (h : SemiOpen A) : SemiOpen (closure A) := by
  -- Unfold the definition of `SemiOpen` in both the hypothesis and the goal.
  dsimp [SemiOpen] at *
  intro x hx
  -- From the semi–openness of `A` we already know that
  -- `closure A ⊆ closure (interior A)`.
  have hx_clIntA : x ∈ closure (interior A) :=
    (semi_open_superset_closure (A := A) h) hx
  -- We next show that `closure (interior A)` is contained in
  -- `closure (interior (closure A))`.
  have h_subset :
      (closure (interior A) : Set X) ⊆ closure (interior (closure A)) := by
    -- Because `A ⊆ closure A`, we have
    -- `interior A ⊆ interior (closure A)`.
    have h_int :
        (interior A : Set X) ⊆ interior (closure A) := by
      have hA_sub : (A : Set X) ⊆ closure A := by
        intro y hy
        exact subset_closure hy
      exact interior_mono hA_sub
    -- Taking closures preserves inclusions.
    exact closure_mono h_int
  -- Combining the two facts yields the desired membership.
  exact h_subset hx_clIntA

theorem dense_union_of_closure_alpha_open_and_dense {A B : Set X} (hA : AlphaOpen (closure A)) (hB : Dense B) : Dense (A ∪ B) := by
  dsimp [Dense] at hB ⊢
  simpa [closure_union, hB, Set.union_univ]

theorem preopen_union_interiors_is_preopen {A B : Set X} (hA : PreOpen A) (hB : PreOpen B) : PreOpen (interior (A ∪ B)) := by
  dsimp [PreOpen]
  intro x hx
  -- `interior (A ∪ B)` is open, hence a neighbourhood of `x`.
  have h_nhds : (interior (A ∪ B) : Set X) ∈ 𝓝 x :=
    IsOpen.mem_nhds isOpen_interior hx
  -- Therefore its closure is also a neighbourhood of `x`.
  have h_cl_nhds : (closure (interior (A ∪ B)) : Set X) ∈ 𝓝 x :=
    Filter.mem_of_superset h_nhds subset_closure
  -- Hence `x` belongs to the interior of this closure.
  exact (mem_interior_iff_mem_nhds).2 h_cl_nhds

theorem dense_intersection_is_preopen_if_open {A B : Set X} (hA : Dense A) (hB : IsOpen B) : PreOpen (A ∩ B) := by
  -- Unfold the definition of `PreOpen`.
  dsimp [PreOpen]
  intro x hx
  -- From `hx : x ∈ A ∩ B` we get, in particular, `x ∈ B`.
  have hxB : x ∈ B := hx.2
  ----------------------------------------------------------------
  -- Step 1:  prove `B ⊆ interior (closure (A ∩ B))`.
  ----------------------------------------------------------------
  have hB_subset_int : (B : Set X) ⊆ interior (closure ((A ∩ B : Set X))) := by
    -- It suffices to show `B ⊆ closure (A ∩ B)` and then use
    -- maximality of the interior (because `B` is open).
    have hB_subset_cl : (B : Set X) ⊆ closure (A ∩ B : Set X) := by
      intro y hyB
      -- We show that `y ∈ closure (A ∩ B)` using the neighbourhood
      -- characterisation of the closure.
      have : y ∈ closure (A ∩ B : Set X) := by
        apply (mem_closure_iff).2
        intro U hU hyU
        -- Work in the open set `V := U ∩ B`, which contains `y`.
        let V : Set X := U ∩ B
        have hV_open : IsOpen V := hU.inter hB
        have hyV : y ∈ V := by
          dsimp [V]; exact And.intro hyU hyB
        -- Because `A` is dense, `closure A = univ`, hence `y ∈ closure A`.
        have y_closureA : y ∈ closure (A : Set X) := by
          have : (closure (A : Set X)) = (Set.univ : Set X) := hA.closure_eq
          have : y ∈ (Set.univ : Set X) := by
            trivial
          simpa [hA.closure_eq] using this
        -- Apply the neighbourhood characterisation of `closure A`
        -- with the open set `V`.
        have h_nonempty : (V ∩ A).Nonempty :=
          (mem_closure_iff).1 y_closureA V hV_open hyV
        -- Extract a witness in `U ∩ (A ∩ B)`.
        rcases h_nonempty with ⟨z, hz⟩
        have hzV   : z ∈ V := hz.1
        have hzA   : z ∈ A := hz.2
        have hzU   : z ∈ U := hzV.1
        have hzB   : z ∈ B := hzV.2
        exact ⟨z, And.intro hzU (And.intro hzA hzB)⟩
      exact this
    -- Since `B` is open, `B ⊆ interior (closure (A ∩ B))`.
    exact interior_maximal hB_subset_cl hB
  ----------------------------------------------------------------
  -- Step 2:  apply the inclusion obtained in Step 1 to the point `x`.
  ----------------------------------------------------------------
  exact hB_subset_int hxB

theorem dense_union_of_preopen_sets_is_preopen {A B : Set X} (hA : PreOpen A) (hB : PreOpen B) : PreOpen (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA_mem =>
      -- `x ∈ A`
      have hA_int : x ∈ interior (closure A) := hA hA_mem
      -- `closure A ⊆ closure (A ∪ B)`
      have h_sub : (closure A : Set X) ⊆ closure (A ∪ B) := by
        have : (A : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact closure_mono this
      -- Monotonicity of `interior`
      exact (interior_mono h_sub) hA_int
  | inr hB_mem =>
      -- `x ∈ B`
      have hB_int : x ∈ interior (closure B) := hB hB_mem
      -- `closure B ⊆ closure (A ∪ B)`
      have h_sub : (closure B : Set X) ⊆ closure (A ∪ B) := by
        have : (B : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inr hy
        exact closure_mono this
      -- Monotonicity of `interior`
      exact (interior_mono h_sub) hB_int

theorem semi_open_distrib_closure {A B : Set X} (hA : SemiOpen A) (hB : SemiOpen B) : SemiOpen (closure (A ∪ B)) := by
  -- First, we show that `A ∪ B` itself is semi-open.
  have h_union : SemiOpen (A ∪ B) := by
    -- Unfold the definition of `SemiOpen`.
    dsimp [SemiOpen]
    intro x hx
    cases hx with
    | inl hxA =>
        -- `x ∈ A`
        -- Semi-openness of `A` gives `x ∈ closure (interior A)`.
        have hx_clA : x ∈ closure (interior A) := hA hxA
        -- Relate the two closures.
        have h_sub :
            (closure (interior A) : Set X) ⊆
              closure (interior (A ∪ B)) := by
          -- First relate the interiors.
          have h_int :
              (interior A : Set X) ⊆ interior (A ∪ B) := by
            apply interior_mono
            intro y hy
            exact Or.inl hy
          -- Taking closures preserves inclusion.
          exact closure_mono h_int
        exact h_sub hx_clA
    | inr hxB =>
        -- `x ∈ B`
        -- Semi-openness of `B` gives `x ∈ closure (interior B)`.
        have hx_clB : x ∈ closure (interior B) := hB hxB
        -- Relate the two closures.
        have h_sub :
            (closure (interior B) : Set X) ⊆
              closure (interior (A ∪ B)) := by
          -- First relate the interiors.
          have h_int :
              (interior B : Set X) ⊆ interior (A ∪ B) := by
            apply interior_mono
            intro y hy
            exact Or.inr hy
          -- Taking closures preserves inclusion.
          exact closure_mono h_int
        exact h_sub hx_clB
  -- Now, apply `closure_semi_open` to pass to the closure of the union.
  have h_closure : SemiOpen (closure (A ∪ B)) :=
    closure_semi_open (A := A ∪ B) h_union
  simpa using h_closure

theorem alpha_open_intersection_with_semi_open_is_semi_open {A B : Set X} (hA : AlphaOpen A) (hB : SemiOpen B) : SemiOpen (A ∩ B) := by
  simpa [Set.inter_comm] using
    (intersection_of_semi_open_and_alpha_open_is_semi_open hB hA)

theorem dense_intersections_alpha_open_is_preopen {A B : Set X} (hA : AlphaOpen A) (hB : Dense B) : PreOpen (A ∩ B) := by
  -- Unfold `PreOpen`.
  dsimp [PreOpen] at *
  -- Fix a point `x ∈ A ∩ B`.
  intro x hx
  rcases hx with ⟨hxA, hxB⟩

  ----------------------------------------------------------------
  -- 1.  The α–openness of `A` gives a first interior membership.
  ----------------------------------------------------------------
  have hA_int : x ∈ interior (closure (interior A)) := hA hxA

  ----------------------------------------------------------------
  -- 2.  We claim `closure (interior A) ⊆ closure (interior A ∩ B)`.
  --     We first establish the corresponding statement for
  --     `interior A`, then pass to closures.
  ----------------------------------------------------------------
  have h_sub_int :
      (interior A : Set X) ⊆ closure (interior A ∩ B) := by
    intro y hyIntA
    -- We use the neighbourhood characterisation of the closure.
    apply (mem_closure_iff).2
    intro U hU hyU
    -- Work in the non-empty open set `U ∩ interior A`.
    have hU_int_open : IsOpen (U ∩ interior A) := hU.inter isOpen_interior
    have hU_int_nonempty : (U ∩ interior A : Set X).Nonempty :=
      ⟨y, ⟨hyU, hyIntA⟩⟩
    -- Density of `B` gives a point of `B` inside it.
    have h_nonempty :
        ((U ∩ interior A) ∩ B : Set X).Nonempty :=
      hB.inter_open_nonempty (U ∩ interior A) hU_int_open hU_int_nonempty
    rcases h_nonempty with ⟨z, ⟨⟨hzU, hzIntA⟩, hzB⟩⟩
    -- This point lies in `U ∩ (interior A ∩ B)`, as required.
    exact ⟨z, ⟨hzU, ⟨hzIntA, hzB⟩⟩⟩

  -- Passing to closures (the right set is closed).
  have h_closure_subset :
      (closure (interior A) : Set X) ⊆ closure (interior A ∩ B) :=
    closure_minimal h_sub_int isClosed_closure

  ----------------------------------------------------------------
  -- 3.  Compare the two interiors that appear in the goal.
  ----------------------------------------------------------------
  have h_int_subset₁ :
      (interior (closure (interior A)) : Set X) ⊆
        interior (closure (interior A ∩ B)) :=
    interior_mono h_closure_subset

  ----------------------------------------------------------------
  -- 4.  Finally, relate `closure (interior A ∩ B)` to
  --     `closure (A ∩ B)`, then apply the inclusions to `x`.
  ----------------------------------------------------------------
  have h_closure_subset₂ :
      (closure (interior A ∩ B) : Set X) ⊆ closure (A ∩ B) := by
    -- Because `interior A ∩ B ⊆ A ∩ B`.
    have h_sub : ((interior A ∩ B) : Set X) ⊆ (A ∩ B) := by
      intro y hy
      exact ⟨interior_subset hy.1, hy.2⟩
    exact closure_mono h_sub

  have h_int_subset₂ :
      (interior (closure (interior A ∩ B)) : Set X) ⊆
        interior (closure (A ∩ B)) :=
    interior_mono h_closure_subset₂

  -- Apply the chain of inclusions to the initial point `x`.
  exact h_int_subset₂ (h_int_subset₁ hA_int)

theorem interior_union_is_alpha_open {A B : Set X} (hA : IsOpen A) (hB : Dense B) : AlphaOpen (interior (A ∪ B)) := by
  simpa using
    (open_set_is_alpha_open (A := interior (A ∪ B)) isOpen_interior)

theorem dense_union_semi_open_closure_is_semi_open_closure {A B : Set X} (hA : Dense A) (hB : SemiOpen (closure B)) : SemiOpen (closure (A ∪ B)) := by
  dsimp [SemiOpen] at hB ⊢
  -- `A` is dense, so the closure of `A ∪ B` is the whole space.
  have h_closure_union : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : closure (A ∪ B : Set X) =
        closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using (closure_union (A := A) (B := B))
    simpa [hA.closure_eq, Set.univ_union] using this
  -- Now verify the defining inclusion for semi–openness.
  intro x hx
  -- Rewrite `hx` using the fact that the closure is `univ`.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    simpa [h_closure_union] using hx
  -- After rewriting, the goal also reduces to membership in `univ`.
  simpa [h_closure_union, interior_univ, closure_univ] using hx_univ

theorem union_of_dense_and_preopen_closure_is_preopen {A B : Set X} (hA : Dense A) (hB : PreOpen (closure B)) : PreOpen (A ∪ B) := by
  have hA_closure : PreOpen (closure A) := preopen_closure_of_dense_subset hA
  exact preopen_union_is_preopen_if_closure_is_preopen hA_closure hB

theorem interior_closure_of_dense_is_preopen {A : Set X} (h : Dense A) : PreOpen (interior (closure A)) := by
  -- Unfold the definition of `PreOpen`.
  dsimp [PreOpen]
  intro x hx
  -- The set `interior (closure A)` is open.
  have h_open : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  -- Trivially, it is contained in its closure.
  have h_subset :
      (interior (closure (A : Set X)) : Set X) ⊆
        closure (interior (closure (A : Set X))) := by
    intro y hy
    exact subset_closure hy
  -- By maximality of the interior of a closed set we obtain the desired inclusion.
  have h_incl :
      (interior (closure (A : Set X)) : Set X) ⊆
        interior (closure (interior (closure (A : Set X)))) :=
    interior_maximal h_subset h_open
  -- Apply the inclusion to the given point.
  exact h_incl hx

theorem semi_open_intersections_preopen {A B : Set X} (hA : PreOpen A) (hB : SemiOpen B) : SemiOpen (interior (A ∩ B)) := by
  dsimp [SemiOpen]
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem preopen_intersection_of_dense_and_alpha_open {A B : Set X} (hA : Dense A) (hB : AlphaOpen B) : PreOpen (A ∩ B) := by
  simpa [Set.inter_comm] using
    (dense_intersections_alpha_open_is_preopen (A := B) (B := A) hB hA)

theorem dense_union_alpha_open_closure_is_dense {A B : Set X} (hA : AlphaOpen (closure A)) (hB : Dense B) : Dense (A ∪ closure B) := by
  dsimp [Dense] at hB ⊢
  simpa [closure_union, closure_closure, hB, Set.univ_union]

theorem semi_open_update_empty_union {A B : Set X} (hA : SemiOpen A) (hB : SemiOpen B) : SemiOpen (B ∪ A \ B) := by
  -- Unfold `SemiOpen` in the hypotheses.
  dsimp [SemiOpen] at hA hB
  -- Unfold `SemiOpen` in the goal.
  dsimp [SemiOpen]
  -- Take an arbitrary point `x` in the union.
  intro x hx
  -- Analyse the two possibilities for `x`.
  cases hx with
  | inl hxB =>
      -- Case `x ∈ B`.
      -- Use the semi–openness of `B`.
      have hB_cl : x ∈ closure (interior B) := hB hxB
      -- Relate the two closures via monotonicity.
      have h_sub_int :
          (interior B : Set X) ⊆ interior (B ∪ (A \ B)) := by
        -- `B ⊆ B ∪ (A \ B)`.
        have h_sub : (B : Set X) ⊆ (B ∪ (A \ B)) := by
          intro y hy; exact Or.inl hy
        exact interior_mono h_sub
      have h_sub_cl :
          (closure (interior B) : Set X) ⊆
            closure (interior (B ∪ (A \ B))) :=
        closure_mono h_sub_int
      exact h_sub_cl hB_cl
  | inr hxA_diff =>
      -- Case `x ∈ A \ B`.
      -- Extract the membership in `A`.
      have hxA : x ∈ A := hxA_diff.1
      -- Use the semi–openness of `A`.
      have hA_cl : x ∈ closure (interior A) := hA hxA
      -- Relate the two closures via monotonicity.
      have h_sub_int :
          (interior A : Set X) ⊆ interior (B ∪ (A \ B)) := by
        -- Show `A ⊆ B ∪ (A \ B)`.
        have h_sub : (A : Set X) ⊆ (B ∪ (A \ B)) := by
          intro y hyA
          by_cases hBy : y ∈ B
          · exact Or.inl hBy
          · exact Or.inr ⟨hyA, hBy⟩
        exact interior_mono h_sub
      have h_sub_cl :
          (closure (interior A) : Set X) ⊆
            closure (interior (B ∪ (A \ B))) :=
        closure_mono h_sub_int
      exact h_sub_cl hA_cl

theorem extension_of_dense_with_alpha_open {A B : Set X} (hA : Dense A) (hB : AlphaOpen B) : Dense (closure (A ∪ closure B)) := by
  dsimp [Dense] at hA ⊢
  simpa [closure_closure, closure_union, hA, Set.univ_union]

theorem minimal_extension_of_semi_open_to_alpha_open {A : Set X} (hA : SemiOpen A) : ∃ B, AlphaOpen B ∧ A ⊆ B := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa using
      (open_set_is_alpha_open (A := (Set.univ : Set X)) isOpen_univ)
  · exact Set.subset_univ _

theorem closure_of_semi_open_and_open {A B : Set X} (hA : SemiOpen A) (hB : IsOpen B) : SemiOpen (closure (A ∪ B)) := by
  have hB_alpha : AlphaOpen B := open_set_is_alpha_open hB
  simpa using closure_of_semi_open_union_alpha_open hA hB_alpha

theorem dense_union_alpha_open_is_dense {A B : Set X} (hA : Dense A) (hB : AlphaOpen B) : Dense (A ∪ B) := by
  simpa [Set.union_comm] using
    (union_preopen_is_dense_if_alpha_open_and_dense (A := B) (B := A) hB hA)

theorem dense_of_semi_open_closure_union {A B : Set X} (hA : SemiOpen (closure A)) (hB : Dense B) : Dense (A ∪ closure B) := by
  dsimp [Dense] at hB ⊢
  simpa [closure_union, closure_closure, hB, Set.union_univ, Set.univ_union]

theorem semi_open_interior_union_alpha_open {A B : Set X} (hA : SemiOpen A) (hB : AlphaOpen B) : SemiOpen (interior (A ∪ B)) := by
  dsimp [SemiOpen]
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem closure_of_union_of_dense_and_semi_open_is_dense {A B : Set X} (hA : Dense A) (hB : SemiOpen B) : Dense (closure (A ∪ B)) := by
  dsimp [Dense] at hA ⊢
  simpa [closure_union, hA, Set.univ_union, closure_closure]

theorem semi_open_complement_union_dense_is_dense {A B : Set X} (hA : SemiOpen A) (hB : Dense B) : Dense (Aᶜ ∪ B) := by
  dsimp [Dense] at hB ⊢
  simpa [closure_union, hB, Set.union_univ]

theorem closure_partial_intersection_of_semi_open_and_dense {A B : Set X} (hA : SemiOpen A) (hB : Dense B) : SemiOpen (closure (A ∩ B)) := by
  -- Unfold the definition of `SemiOpen`.
  dsimp [SemiOpen]
  intro x hx
  ----------------------------------------------------------------
  -- Step 1: `closure (A ∩ B) ⊆ closure A`.
  ----------------------------------------------------------------
  have h₁ : (closure (A ∩ B : Set X)) ⊆ closure (A : Set X) := by
    exact closure_mono (by
      intro y hy
      exact hy.1)
  have hx₁ : x ∈ closure (A : Set X) := h₁ hx
  ----------------------------------------------------------------
  -- Step 2: `closure A ⊆ closure (interior A)` by semi–openness of `A`.
  ----------------------------------------------------------------
  have hx₂ : x ∈ closure (interior A) :=
    (semi_open_superset_closure (A := A) hA) hx₁
  ----------------------------------------------------------------
  -- Step 3:  we prove `interior A ⊆ interior (closure (A ∩ B))`.
  ----------------------------------------------------------------
  have h_int_subset :
      (interior A : Set X) ⊆ interior (closure (A ∩ B)) := by
    -- First, show  `interior A ⊆ closure (A ∩ B)`.
    have h_sub_cl : (interior A : Set X) ⊆ closure (A ∩ B) := by
      intro y hyIntA
      -- Use the neighbourhood characterisation of the closure.
      have : y ∈ closure (A ∩ B) := by
        apply (mem_closure_iff).2
        intro U hU hyU
        -- Work inside the open set `U ∩ interior A`.
        have hWU : IsOpen (U ∩ interior A) := hU.inter isOpen_interior
        have hyWU : y ∈ U ∩ interior A := ⟨hyU, hyIntA⟩
        -- This set is non-empty; density of `B` gives a point of `B` in it.
        have h_nonempty : ((U ∩ interior A) ∩ B).Nonempty :=
          hB.inter_open_nonempty (U ∩ interior A) hWU ⟨y, hyWU⟩
        rcases h_nonempty with ⟨z, ⟨⟨hzU, hzIntA⟩, hzB⟩⟩
        -- The point `z` lies in `U ∩ (A ∩ B)`.
        exact ⟨z, ⟨hzU, ⟨(interior_subset hzIntA), hzB⟩⟩⟩
      simpa using this
    -- Use maximality of the interior (since `interior A` is open).
    exact interior_maximal h_sub_cl isOpen_interior
  ----------------------------------------------------------------
  -- Step 4:  take closures to get
  --   `closure (interior A) ⊆ closure (interior (closure (A ∩ B)))`.
  ----------------------------------------------------------------
  have h_closure_subset :
      (closure (interior A) : Set X) ⊆
        closure (interior (closure (A ∩ B))) :=
    closure_mono h_int_subset
  ----------------------------------------------------------------
  -- Step 5:  assemble the chain of inclusions.
  ----------------------------------------------------------------
  have h_chain :
      (closure (A ∩ B : Set X)) ⊆
        closure (interior (closure (A ∩ B))) := by
    -- `closure (A ∩ B) ⊆ closure A`
    have h₀ : (closure (A ∩ B : Set X)) ⊆ closure (A : Set X) := h₁
    -- `closure A ⊆ closure (interior A)`
    have h₁' : (closure (A : Set X)) ⊆ closure (interior A) :=
      semi_open_superset_closure (A := A) hA
    exact
      (Set.Subset.trans h₀ (Set.Subset.trans h₁' h_closure_subset))
  ----------------------------------------------------------------
  -- Step 6:  apply the inclusion to the given point.
  ----------------------------------------------------------------
  exact h_chain hx

theorem open_union_preopen_is_preopen {A B : Set X} (hA : IsOpen A) (hB : PreOpen B) : PreOpen (A ∪ B) := by
  have hA_alpha : AlphaOpen A := open_set_is_alpha_open hA
  exact union_of_alpha_open_and_preopen_is_preopen hA_alpha hB

theorem dense_union_with_semi_open_is_dense {A B : Set X} (hA : Dense A) (hB : SemiOpen B) : Dense (A ∪ closure B) := by
  dsimp [Dense] at hA ⊢
  simpa [closure_union, closure_closure, hA, Set.univ_union]

theorem intersection_of_dense_and_semi_open_is_semi_open {A B : Set X} (hA : Dense A) (hB : SemiOpen B) : SemiOpen (closure (A ∩ B)) := by
  simpa [Set.inter_comm] using
    (closure_partial_intersection_of_semi_open_and_dense (A := B) (B := A) hB hA)

theorem alpha_open_difference_interclosure {A B : Set X} (hA : AlphaOpen A) : AlphaOpen (A \ closure B) := by
  -- Unfold `AlphaOpen` and introduce a point `x`.
  intro x hx
  -- Split the membership information for `x`.
  rcases hx with ⟨hxA, hxNotClB⟩
  -- From the α-openness of `A` we have
  have hxInt :
      x ∈ interior (closure (interior A)) := hA hxA
  -- `N := (closure B)ᶜ` is an open neighbourhood of `x`.
  have hN_open : IsOpen ((closure (B : Set X))ᶜ) :=
    isClosed_closure.isOpen_compl
  have hxN : x ∈ (closure (B : Set X))ᶜ := by
    simpa using hxNotClB
  -- Consider the open set
  --   `W := interior (closure (interior A)) ∩ N`
  -- which contains `x`.
  let W : Set X :=
    interior (closure (interior A)) ∩ (closure (B : Set X))ᶜ
  have hW_open : IsOpen W :=
    isOpen_interior.inter hN_open
  have hxW : x ∈ W := by
    exact ⟨hxInt, hxN⟩
  ------------------------------------------------------------------
  -- We show `W ⊆ closure (interior (A \ closure B))`.
  ------------------------------------------------------------------
  have hW_subset :
      (W : Set X) ⊆ closure (interior (A \ closure B)) := by
    intro y hyW
    -- Split the information carried by `hyW`.
    rcases hyW with ⟨hyInt, hyNotClB⟩
    -- `y` lies in `closure (interior A)`.
    have hyClIntA : y ∈ closure (interior A) :=
      (interior_subset : interior (closure (interior A)) ⊆
        closure (interior A)) hyInt
    ----------------------------------------------------------------
    -- Use the neighbourhood characterisation of the closure to show
    -- `y ∈ closure (interior (A \ closure B))`.
    ----------------------------------------------------------------
    apply (mem_closure_iff).2
    intro U hU hyU
    -- Intersect `U` with `N` to stay away from `B`.
    have hU'open : IsOpen (U ∩ (closure (B : Set X))ᶜ) :=
      hU.inter hN_open
    have hyU' : y ∈ U ∩ (closure (B : Set X))ᶜ := ⟨hyU, hyNotClB⟩
    -- `y ∈ closure (interior A)` ⇒ this neighbourhood meets `interior A`.
    obtain ⟨z, ⟨⟨hzU, hzNotClB⟩, hzIntA⟩⟩ :
        ((U ∩ (closure (B : Set X))ᶜ) ∩ interior A).Nonempty := by
      have :=
        (mem_closure_iff).1 hyClIntA (U ∩ (closure (B : Set X))ᶜ)
          hU'open hyU'
      simpa [Set.inter_assoc, Set.inter_left_comm,
        Set.inter_right_comm] using this
    -- Show that `z ∈ interior (A \ closure B)`.
    have hzIntDiff : z ∈ interior (A \ closure B) := by
      -- The open set `interior A ∩ (closure B)ᶜ` contains `z`
      -- and is contained in `A \ closure B`.
      have hO_open : IsOpen (interior A ∩ (closure (B : Set X))ᶜ) :=
        isOpen_interior.inter hN_open
      have hO_subset :
          (interior A ∩ (closure (B : Set X))ᶜ : Set X) ⊆
            (A \ closure B) := by
        intro t ht
        rcases ht with ⟨htIntA, htNotClB⟩
        exact ⟨interior_subset htIntA, htNotClB⟩
      have hz_memO : z ∈ (interior A ∩ (closure (B : Set X))ᶜ) :=
        ⟨hzIntA, hzNotClB⟩
      have hO_to_int :
          (interior A ∩ (closure (B : Set X))ᶜ : Set X) ⊆
            interior (A \ closure B) :=
        interior_maximal hO_subset hO_open
      exact hO_to_int hz_memO
    -- Finally, `z` lies in `U ∩ interior (A \ closure B)`, as desired.
    exact ⟨z, ⟨hzU, hzIntDiff⟩⟩
  ------------------------------------------------------------------
  -- `W` is an open neighbourhood of `x` contained in the required
  -- closed set, hence `x` lies in its interior.
  ------------------------------------------------------------------
  have h_cl_nhds :
      (closure (interior (A \ closure B)) : Set X) ∈ 𝓝 x := by
    have hW_nhds : (W : Set X) ∈ 𝓝 x :=
      hW_open.mem_nhds hxW
    exact Filter.mem_of_superset hW_nhds hW_subset
  -- Translate the neighbourhood membership into the interior one.
  exact
    (mem_interior_iff_mem_nhds).2 h_cl_nhds

theorem closure_of_dense_union_is_alpha_open {A B : Set X} (hA : Dense A) (hB : AlphaOpen B) : AlphaOpen (closure (A ∪ B)) := by
  -- Compute the closure of `A ∪ B`; density of `A` makes it the whole space.
  have h_closure_union : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    simpa [hA.closure_eq, Set.univ_union] using
      (closure_union (A := A) (B := B))
  -- `univ` is open, hence α-open.
  have h_alpha_univ : AlphaOpen (Set.univ : Set X) := by
    simpa using
      (open_set_is_alpha_open (A := (Set.univ : Set X)) isOpen_univ)
  -- Transfer the result through the above identification.
  simpa [h_closure_union] using h_alpha_univ

theorem semi_open_inter_union_alpha_open {A B : Set X} (hA : SemiOpen A) (hB : AlphaOpen B) : SemiOpen (A ∪ interior B) := by
  -- Unfold `SemiOpen` in the hypotheses and the goal.
  dsimp [SemiOpen] at hA hB ⊢
  -- Fix a point `x ∈ A ∪ interior B`.
  intro x hx
  -- Analyse the two possible cases for `x`.
  cases hx with
  | inl hxA =>
      -- Case `x ∈ A`.
      -- Semi–openness of `A` gives `x ∈ closure (interior A)`.
      have hx_clA : x ∈ closure (interior A) := hA hxA
      -- Relate the two closures via monotonicity.
      have h_sub_int :
          (interior A : Set X) ⊆ interior (A ∪ interior B) := by
        -- Because `A ⊆ A ∪ interior B`.
        have h_sub : (A : Set X) ⊆ A ∪ interior B := by
          intro y hy; exact Or.inl hy
        exact interior_mono h_sub
      have h_sub_cl :
          (closure (interior A) : Set X) ⊆
            closure (interior (A ∪ interior B)) :=
        closure_mono h_sub_int
      -- Conclude.
      exact h_sub_cl hx_clA
  | inr hxIntB =>
      -- Case `x ∈ interior B`.
      -- First move to the closure of `interior B`.
      have hx_clIntB : x ∈ closure (interior B) :=
        subset_closure hxIntB
      -- Relate the two closures via monotonicity.
      have h_sub_int :
          (interior B : Set X) ⊆ interior (A ∪ interior B) := by
        -- `interior B` is open and contained in the union.
        have h_open : IsOpen (interior B) := isOpen_interior
        have h_sub  : (interior B : Set X) ⊆ A ∪ interior B := by
          intro y hy; exact Or.inr hy
        exact interior_maximal h_sub h_open
      have h_sub_cl :
          (closure (interior B) : Set X) ⊆
            closure (interior (A ∪ interior B)) :=
        closure_mono h_sub_int
      -- Conclude.
      exact h_sub_cl hx_clIntB

theorem intersection_with_alpha_open_gives_preopen {A B : Set X} (hA : IsOpen A) (hB : AlphaOpen B) : PreOpen (A ∩ B) := by
  -- First, an open set is preopen.
  have hA_pre : PreOpen A := by
    dsimp [PreOpen]
    intro x hx
    -- `A` is an open neighbourhood of `x`.
    have h_nhds : (A : Set X) ∈ 𝓝 x := hA.mem_nhds hx
    -- Hence its closure is also a neighbourhood of `x`.
    have h_cl_nhds : (closure A : Set X) ∈ 𝓝 x :=
      Filter.mem_of_superset h_nhds subset_closure
    -- Therefore `x` is in the desired interior.
    exact (mem_interior_iff_mem_nhds).2 h_cl_nhds
  -- Apply the lemma for the intersection of an α-open and a preopen set.
  simpa [Set.inter_comm] using
    (preopen_intersection_of_alpha_open (A := B) (B := A) hB hA_pre)

theorem union_of_consecutive_alpha_open_sets_is_alpha_open {A B : Set X} (hA : AlphaOpen A) (hB : AlphaOpen B) : AlphaOpen (⋃ x ∈ A, B) := by
  -- Unfold `AlphaOpen`
  dsimp [AlphaOpen]
  -- Take a point lying in the big union
  intro x hx
  -- Extract witnesses `y : X`, `hyA : y ∈ A`, and `hxB : x ∈ B`
  rcases Set.mem_iUnion.1 hx with ⟨y, hxy⟩
  rcases Set.mem_iUnion.1 hxy with ⟨hyA, hxB⟩
  -- From the α-openness of `B` we have the required interior membership
  have hB_int : x ∈ interior (closure (interior B)) := hB hxB
  ------------------------------------------------------------------
  -- Since `y ∈ A`, the set `A` is non-empty.  Choose `a ∈ A`.
  ------------------------------------------------------------------
  have hA_nonempty : (A : Set X).Nonempty := ⟨y, hyA⟩
  rcases hA_nonempty with ⟨a, haA⟩
  ------------------------------------------------------------------
  -- `B ⊆ ⋃ x ∈ A, B` because the union contains the copy indexed by `a`.
  ------------------------------------------------------------------
  have hB_sub_union : (B : Set X) ⊆ ⋃ z ∈ A, B := by
    intro z hzB
    exact
      Set.mem_iUnion.2
        ⟨a, Set.mem_iUnion.2 ⟨haA, hzB⟩⟩
  -- Consequently, `interior B ⊆ interior (⋃ x ∈ A, B)`.
  have h_int_subset :
      (interior B : Set X) ⊆ interior (⋃ z ∈ A, B) :=
    interior_mono hB_sub_union
  -- Taking closures preserves inclusion.
  have h_closure_subset :
      (closure (interior B) : Set X) ⊆
        closure (interior (⋃ z ∈ A, B)) :=
    closure_mono h_int_subset
  -- Apply monotonicity of `interior` to transport the membership of `x`.
  exact (interior_mono h_closure_subset) hB_int

theorem alpha_open_decreasing_union {I : Type*} [Finite I] {f : I → Set X} (h : ∀ i, AlphaOpen (f i)) : AlphaOpen (⋂ i, f i) := by
  simpa using
    (finite_intersection_of_alpha_open_sets_is_alpha_open (I := I) (f := f) h)

theorem semi_open_of_preopen_and_transitive_closure {A : Set X} (h : PreOpen A) : SemiOpen (closure (A ∪ closure A)) := by
  -- Unfold `SemiOpen` and introduce the point `x`.
  dsimp [SemiOpen]
  intro x hx
  -- First, compute the closure appearing in the goal.
  have h_closure_union : (closure (A ∪ closure A : Set X)) = closure A := by
    calc
      closure (A ∪ closure A : Set X)
          = closure A ∪ closure (closure A) := by
            simpa using closure_union (A := A) (B := closure A)
      _ = closure A ∪ closure A := by
            simpa [closure_closure]
      _ = closure A := by
            simp
  -- Transport `hx` along the above equality.
  have hx' : x ∈ closure A := by
    simpa [h_closure_union] using hx
  ------------------------------------------------------------------
  -- We show that `x ∈ closure (interior (closure A))`.
  ------------------------------------------------------------------
  have hx_goal : x ∈ closure (interior (closure A)) := by
    -- Use the neighbourhood characterisation of the closure.
    apply (mem_closure_iff).2
    intro U hU hxU
    -- Because `x ∈ closure A`, the neighbourhood `U` meets `A`.
    have h_nonempty : ((U ∩ A : Set X)).Nonempty :=
      (mem_closure_iff).1 hx' U hU hxU
    -- Extract a witness `y`.
    rcases h_nonempty with ⟨y, ⟨hyU, hyA⟩⟩
    -- Since `A` is preopen, `y ∈ interior (closure A)`.
    have hy_int : y ∈ interior (closure A) := h hyA
    -- Provide the required witness in `U ∩ interior (closure A)`.
    exact ⟨y, ⟨hyU, hy_int⟩⟩
  -- Conclude using `h_closure_union`.
  simpa [h_closure_union] using hx_goal

theorem intersection_semi_open_subset {A B : Set X} (hA : SemiOpen A) : (A ∩ B ⊆ closure (interior A)) := by
  intro x hx
  exact hA hx.1

theorem dense_union_of_preopen_and_dense_is_preopen {A B : Set X} (hA : PreOpen A) (hB : Dense B) : PreOpen (A ∪ B) := by
  -- Unfold the definition of `PreOpen`.
  dsimp [PreOpen] at *
  intro x hx
  -- Because `B` is dense, `closure B = univ`, so the closure of `A ∪ B` is `univ`.
  have h_closure_union : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : closure (A ∪ B : Set X) = closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using (closure_union (A := A) (B := B))
    simpa [hB.closure_eq, Set.union_univ] using this
  -- Trivially, every point belongs to `univ`.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  -- Rewriting with the computed closure gives the desired membership.
  simpa [h_closure_union, interior_univ] using this

theorem interior_of_semi_open_is_preopen {A : Set X} (h : SemiOpen A) : PreOpen (interior A) := by
  intro x hx
  -- `interior A` is open and contained in its own closure,
  -- hence it is contained in the interior of that closure.
  have h_sub :
      (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal (subset_closure) isOpen_interior
  exact h_sub hx

theorem infinite_union_of_alpha_open_sets_is_alpha_open {I : Type*} {f : I → Set X} (h : ∀ i, AlphaOpen (f i)) : AlphaOpen (⋃ i, f i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  -- `x` belongs to the interior associated with `f i`.
  have hx_int : x ∈ interior (closure (interior (f i))) := (h i) hxi
  -- We compare the two interiors that appear.
  have h_subset :
      (interior (closure (interior (f i))) : Set X) ⊆
        interior (closure (interior (⋃ j, f j))) := by
    -- First compare the corresponding closures.
    have h_closure_subset :
        (closure (interior (f i)) : Set X) ⊆
          closure (interior (⋃ j, f j)) := by
      -- It suffices to compare the two interiors inside the closures.
      have h_int_subset :
          (interior (f i) : Set X) ⊆ interior (⋃ j, f j) := by
        -- `f i ⊆ ⋃ j, f j`, hence the same for interiors.
        have h_sub : (f i : Set X) ⊆ ⋃ j, f j := by
          intro y hy
          exact Set.mem_iUnion.2 ⟨i, hy⟩
        exact interior_mono h_sub
      exact closure_mono h_int_subset
    -- Apply monotonicity of `interior`.
    exact interior_mono h_closure_subset
  exact h_subset hx_int

theorem interior_of_preopen_closure_is_alpha_open {A : Set X} (hA : PreOpen (closure A)) : AlphaOpen (interior A) := by
  dsimp [AlphaOpen]
  intro x hx
  -- `interior A` is open, hence a neighbourhood of `x`.
  have h_nhds : (interior A : Set X) ∈ 𝓝 x :=
    IsOpen.mem_nhds isOpen_interior hx
  -- Therefore its closure is also a neighbourhood of `x`.
  have h_cl_nhds : (closure (interior A) : Set X) ∈ 𝓝 x :=
    Filter.mem_of_superset h_nhds subset_closure
  -- Hence `x` lies in the interior of this closure.
  have h_mem : x ∈ interior (closure (interior A)) :=
    (mem_interior_iff_mem_nhds).2 h_cl_nhds
  simpa [interior_interior] using h_mem

theorem dense_union_of_opens_is_preopen {A B : Set X} (hA : Dense A) (hB : IsOpen B) : PreOpen (A ∪ B) := by
  dsimp [PreOpen]
  intro x hx
  -- `A` is dense, hence its closure is `univ`, which forces the closure
  -- of the union to be `univ` as well.
  have h_closure_union : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : (closure (A ∪ B : Set X)) = closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using closure_union (A := A) (B := B)
    simpa [hA.closure_eq, Set.univ_union] using this
  -- Trivially, every point belongs to `univ`.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  -- Rewrite with the computed closure.
  simpa [h_closure_union, interior_univ] using this

theorem dense_closure_union_with_preopen {A B : Set X} (hA : Dense A) (hB : PreOpen B) : Dense (closure (A ∪ B)) := by
  dsimp [Dense] at hA ⊢
  simp [closure_union, hA, Set.univ_union, closure_closure]

theorem semi_open_of_decreasing_alpha_open_inter {I : Type*} (f : I → Set X) [Finite I] (h : ∀ i, AlphaOpen (f i)) : SemiOpen (⋂ i, f i) := by
  -- First, the finite intersection of α-open sets is α-open.
  have hAlpha : AlphaOpen (⋂ i, f i) :=
    finite_intersection_of_alpha_open_sets_is_alpha_open (I := I) (f := f) h
  -- Every α-open set is semi-open.
  exact alpha_open_implies_semi_open hAlpha

theorem dense_union_with_closure_is_dense {A B : Set X} (hA : Dense A) (hB : Dense B) : Dense (A ∪ closure B) := by
  dsimp [Dense] at hA hB ⊢
  simpa [closure_union, closure_closure, hA, hB, Set.union_univ, Set.univ_union]

theorem intersection_of_three_alpha_open_is_alpha_open {A B C : Set X} (hA : AlphaOpen A) (hB : AlphaOpen B) (hC : AlphaOpen C) : AlphaOpen (A ∩ B ∩ C) := by
  -- First, the intersection of `A` and `B` is α-open.
  have hAB : AlphaOpen (A ∩ B) :=
    intersection_of_alpha_open_sets_is_alpha_open hA hB
  -- Intersect this set with `C` and rewrite the parentheses.
  simpa [Set.inter_assoc] using
    (intersection_of_alpha_open_sets_is_alpha_open (A := A ∩ B) (B := C) hAB hC)

theorem semi_open_closure_of_preopen_closure {A : Set X} (h : PreOpen (closure A)) : SemiOpen (closure (A ∩ Aᶜ)) := by
  simpa [SemiOpen, Set.inter_compl_self, closure_empty, interior_empty] using
    (Set.empty_subset _)

theorem interior_of_union_with_semi_open {A B : Set X} (hB : SemiOpen B) : SemiOpen (interior (A ∪ B)) := by
  dsimp [SemiOpen] at *
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem sem_open_if_disjoint_closure_intersection {A B : Set X} (hA : SemiOpen A) (hB : IsClosed B) : SemiOpen (A ∩ Bᶜ) := by
  -- Unfold `SemiOpen` in the hypothesis and in the goal.
  dsimp [SemiOpen] at hA ⊢
  -- Fix a point `x ∈ A ∩ Bᶜ`.
  intro x hx
  rcases hx with ⟨hxA, hxBcompl⟩
  -- From the semi–openness of `A` we get `x ∈ closure (interior A)`.
  have hx_clIntA : x ∈ closure (interior A) := hA hxA
  ------------------------------------------------------------------
  -- Goal: `x ∈ closure (interior (A ∩ Bᶜ))`.
  ------------------------------------------------------------------
  apply
    (mem_closure_iff).2
  intro U hU hxU
  ------------------------------------------------------------------
  -- Work in the open neighbourhood `U ∩ Bᶜ` of `x`.
  ------------------------------------------------------------------
  have hBopen : IsOpen (Bᶜ : Set X) := hB.isOpen_compl
  have hV_open : IsOpen (U ∩ Bᶜ) := hU.inter hBopen
  have hxV : x ∈ U ∩ Bᶜ := ⟨hxU, hxBcompl⟩
  -- Since `x ∈ closure (interior A)`, this neighbourhood meets
  -- `interior A`.
  obtain ⟨y, ⟨⟨hyU, hyBcompl⟩, hyIntA⟩⟩ :
      ((U ∩ Bᶜ) ∩ interior A).Nonempty :=
    (mem_closure_iff).1 hx_clIntA (U ∩ Bᶜ) hV_open hxV
  ------------------------------------------------------------------
  -- Show that `y ∈ interior (A ∩ Bᶜ)`.
  ------------------------------------------------------------------
  have hyInt : y ∈ interior (A ∩ Bᶜ) := by
    -- Consider the open set `interior A ∩ Bᶜ`.
    have hO_open : IsOpen (interior A ∩ Bᶜ) :=
      isOpen_interior.inter hBopen
    -- It is contained in `A ∩ Bᶜ`.
    have hO_subset :
        (interior A ∩ Bᶜ : Set X) ⊆ (A ∩ Bᶜ) := by
      intro z hz
      exact ⟨interior_subset hz.1, hz.2⟩
    -- Maximality of interior furnishes the inclusion.
    have h_to_int :
        (interior A ∩ Bᶜ : Set X) ⊆ interior (A ∩ Bᶜ) :=
      interior_maximal hO_subset hO_open
    -- Apply it to `y`.
    exact h_to_int ⟨hyIntA, hyBcompl⟩
  ------------------------------------------------------------------
  -- Provide the required witness in `U ∩ interior (A ∩ Bᶜ)`.
  ------------------------------------------------------------------
  exact ⟨y, ⟨hyU, hyInt⟩⟩

theorem finite_union_of_semi_open_closures_is_semi_open {I : Type*} [Finite I] {f : I → Set X} (h : ∀ i, SemiOpen (closure (f i))) : SemiOpen (closure (⋃ i, f i)) := by
  classical
  ------------------------------------------------------------------
  -- 1.  The finite union of the sets `closure (f i)` is semi-open.
  ------------------------------------------------------------------
  have h_union : SemiOpen (⋃ i, closure (f i)) :=
    finite_union_of_semi_open_sets_is_semi_open
      (I := I) (f := fun i : I => closure (f i)) (by
        intro i; exact h i)

  ------------------------------------------------------------------
  -- 2.  Taking the closure preserves semi-openness (`closure_semi_open`).
  ------------------------------------------------------------------
  have h_closure_union_closures :
      SemiOpen (closure (⋃ i, closure (f i))) :=
    closure_semi_open (A := ⋃ i, closure (f i)) h_union

  ------------------------------------------------------------------
  -- 3.  Show that this closure equals `closure (⋃ i, f i)`.
  ------------------------------------------------------------------
  have h_closure_eq :
      (closure (⋃ i, closure (f i)) : Set X) = closure (⋃ i, f i) := by
    apply Set.Subset.antisymm
    · ----------------------------------------------------------------
      -- `closure (⋃ i, closure (f i)) ⊆ closure (⋃ i, f i)`
      ----------------------------------------------------------------
      -- First, `⋃ i, closure (f i) ⊆ closure (⋃ i, f i)`.
      have h_subset : (⋃ i, closure (f i) : Set X) ⊆
          closure (⋃ j, f j) := by
        intro x hx
        rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
        -- `closure (f i) ⊆ closure (⋃ j, f j)`
        have h_sub : (closure (f i) : Set X) ⊆ closure (⋃ j, f j) := by
          apply closure_mono
          intro y hy
          exact Set.mem_iUnion.2 ⟨i, hy⟩
        exact h_sub hx_i
      -- Apply `closure_mono` and remove the double closure.
      have :
          (closure (⋃ i, closure (f i)) : Set X) ⊆
            closure (closure (⋃ j, f j)) :=
        closure_mono h_subset
      simpa [closure_closure] using this
    · ----------------------------------------------------------------
      -- `closure (⋃ i, f i) ⊆ closure (⋃ i, closure (f i))`
      ----------------------------------------------------------------
      -- Because `⋃ i, f i ⊆ ⋃ i, closure (f i)`.
      have h_subset : (⋃ i, f i : Set X) ⊆ ⋃ i, closure (f i) := by
        intro x hx
        rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
        exact Set.mem_iUnion.2 ⟨i, subset_closure hx_i⟩
      exact closure_mono h_subset

  ------------------------------------------------------------------
  -- 4.  Transport semi-openness through the established equality.
  ------------------------------------------------------------------
  simpa [h_closure_eq] using h_closure_union_closures

theorem closure_of_preopen_and_dense_is_dense {A B : Set X} (hA : PreOpen A) (hB : Dense B) : Dense (closure (A ∪ B)) := by
  dsimp [Dense] at hB ⊢
  simp [closure_closure, closure_union, hB, Set.union_univ]

theorem intersection_of_preopen_closure_and_alpha_open {A B : Set X} (hA : PreOpen (closure A)) (hB : AlphaOpen B) : PreOpen (A ∩ B) := by
  -- Unfold the definition of `PreOpen` in the hypothesis.
  dsimp [PreOpen] at hA
  -- Unfold the definition of `PreOpen` in the goal.
  dsimp [PreOpen]
  -- Fix a point `x ∈ A ∩ B`.
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  --------------------------------------------------------------------
  -- Step 1: obtain two convenient open neighbourhoods of `x`.
  --------------------------------------------------------------------
  -- From `hA : PreOpen (closure A)` we get `x ∈ interior (closure A)`.
  have hA_int : x ∈ interior (closure (A : Set X)) := by
    -- `x ∈ A ⊆ closure A`.
    have hx_clA : x ∈ closure (A : Set X) := subset_closure hxA
    -- Apply the inclusion supplied by `hA`.
    have : x ∈ interior (closure (closure (A : Set X))) := hA hx_clA
    -- Remove the redundant closure.
    simpa [closure_closure] using this
  -- From the α–openness of `B` we obtain
  have hB_int : x ∈ interior (closure (interior (B : Set X))) :=
    hB hxB
  --------------------------------------------------------------------
  -- Step 2: consider the open set  
  --   `U := interior (closure A) ∩ interior (closure (interior B))`
  -- which contains `x`.
  --------------------------------------------------------------------
  set U : Set X :=
      interior (closure (A : Set X)) ∩
        interior (closure (interior (B : Set X))) with hU_def
  have hU_open : IsOpen U := by
    dsimp [hU_def]
    exact isOpen_interior.inter isOpen_interior
  have hxU : x ∈ U := by
    dsimp [hU_def]
    exact ⟨hA_int, hB_int⟩
  --------------------------------------------------------------------
  -- Step 3: we show `U ⊆ closure (A ∩ B)`.
  --------------------------------------------------------------------
  have hU_subset : (U : Set X) ⊆ closure (A ∩ B) := by
    intro y hyU
    -- Split the membership information for `y`.
    rcases hyU with ⟨hyIntA, hyIntClIntB⟩
    -- `y ∈ closure A`.
    have hy_clA : y ∈ closure (A : Set X) :=
      (interior_subset : interior (closure (A : Set X)) ⊆ closure A) hyIntA
    -- `y ∈ closure (interior B)`.
    have hy_clIntB : y ∈ closure (interior (B : Set X)) :=
      (interior_subset :
          interior (closure (interior (B : Set X))) ⊆
            closure (interior (B : Set X))) hyIntClIntB
    ----------------------------------------------------------------
    -- Neighbourhood characterisation of the closure.
    ----------------------------------------------------------------
    apply (mem_closure_iff).2
    intro V hV hyV
    --------------------------------------------------------------
    -- First step: work inside  
    --   `V₁ := V ∩ interior (closure A)`.
    --------------------------------------------------------------
    have hV1_open : IsOpen (V ∩ interior (closure (A : Set X))) :=
      hV.inter isOpen_interior
    have hyV1 : y ∈ V ∩ interior (closure (A : Set X)) :=
      ⟨hyV, hyIntA⟩
    -- Because `y ∈ closure (interior B)`, this neighbourhood meets
    -- `interior B`.
    have h_nonempty₁ :
        ((V ∩ interior (closure (A : Set X))) ∩ interior (B : Set X)).Nonempty :=
      (mem_closure_iff).1 hy_clIntB _ hV1_open hyV1
    rcases h_nonempty₁ with
      ⟨z, ⟨⟨hzV, hzIntClA⟩, hzIntB⟩⟩
    -- `z ∈ closure A`.
    have hz_clA : z ∈ closure (A : Set X) :=
      (interior_subset :
          interior (closure (A : Set X)) ⊆ closure A) hzIntClA
    --------------------------------------------------------------
    -- Second step: work inside  
    --   `V₂ := V ∩ interior B`.
    --------------------------------------------------------------
    have hV2_open : IsOpen (V ∩ interior (B : Set X)) :=
      hV.inter isOpen_interior
    have hzV2 : z ∈ V ∩ interior (B : Set X) := ⟨hzV, hzIntB⟩
    -- Since `z ∈ closure A`, this neighbourhood meets `A`.
    have h_nonempty₂ :
        ((V ∩ interior (B : Set X)) ∩ A).Nonempty :=
      (mem_closure_iff).1 hz_clA _ hV2_open hzV2
    rcases h_nonempty₂ with
      ⟨w, ⟨⟨hwV, hwIntB⟩, hwA⟩⟩
    -- `w ∈ B` because `w ∈ interior B`.
    have hwB : w ∈ B := interior_subset hwIntB
    -- Supply the required witness.
    exact ⟨w, ⟨hwV, ⟨hwA, hwB⟩⟩⟩
  --------------------------------------------------------------------
  -- Step 4: maximality of the interior yields the desired inclusion.
  --------------------------------------------------------------------
  have hU_subset_int :
      (U : Set X) ⊆ interior (closure (A ∩ B)) :=
    interior_maximal hU_subset hU_open
  -- Apply the inclusion to our original point `x`.
  exact hU_subset_int hxU

theorem alpha_open_closure_of_dense_and_open {A B : Set X} (hA : Dense A) (hB : IsOpen B) : AlphaOpen (closure (A ∪ B)) := by
  dsimp [AlphaOpen]
  intro x hx
  -- First, compute the closure of `A ∪ B` using the density of `A`.
  have h_closure_union : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : (closure (A ∪ B : Set X)) =
        closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using (closure_union (A := A) (B := B))
    simpa [hA.closure_eq, Set.univ_union] using this
  -- After rewriting with `h_closure_union`, both the assumption and the goal
  -- reduce to the trivial statement `x ∈ univ`.
  simpa [h_closure_union, interior_univ, closure_univ] using hx

theorem semi_open_closure_of_preopen_union {A B : Set X} (hA : PreOpen A) (hB : PreOpen B) : SemiOpen (closure (A ∪ B)) := by
  -- Unfold the target statement.
  dsimp [SemiOpen]
  -- Fix a point `x ∈ closure (A ∪ B)`.
  intro x hx
  -- We use the neighbourhood characterisation of the closure.
  apply (mem_closure_iff).2
  intro V hV hxV
  -- Because `x ∈ closure (A ∪ B)`, the neighbourhood `V` meets `A ∪ B`.
  have h_nonempty : ((V : Set X) ∩ (A ∪ B)).Nonempty :=
    (mem_closure_iff).1 hx V hV hxV
  -- Choose a witness `y`.
  rcases h_nonempty with ⟨y, ⟨hyV, hyAB⟩⟩
  -- We shall show that `y ∈ interior (closure (A ∪ B))`.
  have hyInt : y ∈ interior (closure (A ∪ B)) := by
    cases hyAB with
    | inl hyA =>
        -- `y ∈ A`, use the pre–openness of `A`.
        have hA_int : y ∈ interior (closure A) := hA hyA
        -- `closure A ⊆ closure (A ∪ B)`.
        have h_sub : (closure (A : Set X)) ⊆ closure (A ∪ B) :=
          closure_mono (by
            intro z hz
            exact Or.inl hz)
        -- Monotonicity of `interior`.
        exact (interior_mono h_sub) hA_int
    | inr hyB =>
        -- `y ∈ B`, use the pre–openness of `B`.
        have hB_int : y ∈ interior (closure B) := hB hyB
        -- `closure B ⊆ closure (A ∪ B)`.
        have h_sub : (closure (B : Set X)) ⊆ closure (A ∪ B) :=
          closure_mono (by
            intro z hz
            exact Or.inr hz)
        -- Monotonicity of `interior`.
        exact (interior_mono h_sub) hB_int
  -- Provide the required witness in `V ∩ interior (closure (A ∪ B))`.
  exact ⟨y, ⟨hyV, hyInt⟩⟩

theorem preopen_union_intersection_is_preopen {A B : Set X} (hA : PreOpen A) (hB : PreOpen B) : PreOpen (A ∪ A ∩ B) := by
  -- First, observe that `A ∪ (A ∩ B) = A`.
  have hEq : (A ∪ A ∩ B : Set X) = A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hA    => exact hA
      | inr hA_B  => exact hA_B.1
    · intro hx
      exact Or.inl hx
  -- Rewriting with this equality turns the goal into `PreOpen A`,
  -- which is given by the hypothesis `hA`.
  simpa [hEq] using hA

theorem dense_closure_of_semi_open_union {A B : Set X} (hA : SemiOpen A) (hB : Dense B) : Dense (closure (A ∪ B)) := by
  dsimp [Dense] at hB ⊢
  simp [closure_closure, closure_union, hB, Set.union_univ]

theorem semi_open_difference_interclosure {A B : Set X} (hA : SemiOpen A) : SemiOpen (A \ closure B) := by
  -- Unfold the definition of `SemiOpen`.
  dsimp [SemiOpen] at hA ⊢
  -- Fix a point `x ∈ A \ closure B`.
  intro x hx
  rcases hx with ⟨hxA, hxNotClB⟩
  -- From the semi-openness of `A` we have
  --   `x ∈ closure (interior A)`.
  have hx_clIntA : x ∈ closure (interior A) := hA hxA
  -- `N := (closure B)ᶜ` is an open neighbourhood of `x`.
  have hN_open : IsOpen ((closure (B : Set X))ᶜ) :=
    isClosed_closure.isOpen_compl
  have hxN : x ∈ (closure (B : Set X))ᶜ := by
    simpa using hxNotClB
  -- We shall prove `x ∈ closure (interior (A \ closure B))`
  -- via the neighbourhood characterisation of the closure.
  apply (mem_closure_iff).2
  intro U hU hxU
  -- Work in the open neighbourhood `V := U ∩ N` of `x`.
  let V : Set X := U ∩ (closure (B : Set X))ᶜ
  have hV_open : IsOpen V := hU.inter hN_open
  have hxV : x ∈ V := by
    dsimp [V]; exact ⟨hxU, hxN⟩
  -- Since `x ∈ closure (interior A)`, `V` meets `interior A`.
  obtain ⟨y, ⟨hyV, hyIntA⟩⟩ :
      (V ∩ interior A).Nonempty :=
    (mem_closure_iff).1 hx_clIntA V hV_open hxV
  -- Split the membership information for `y`.
  have hyU      : y ∈ U := (by
    dsimp [V] at hyV; exact hyV.1)
  have hyNotClB : y ∈ (closure (B : Set X))ᶜ := (by
    dsimp [V] at hyV; exact hyV.2)
  -- Show that `y` actually belongs to `interior (A \ closure B)`.
  have hyIntDiff : y ∈ interior (A \ closure B) := by
    -- The open set `interior A ∩ N` contains `y`
    -- and is contained in `A \ closure B`.
    have hO_open : IsOpen (interior A ∩ (closure (B : Set X))ᶜ) :=
      isOpen_interior.inter hN_open
    have hO_subset :
        (interior A ∩ (closure (B : Set X))ᶜ : Set X) ⊆ (A \ closure B) := by
      intro z hz
      exact ⟨interior_subset hz.1, hz.2⟩
    have hz_mem : y ∈ interior A ∩ (closure (B : Set X))ᶜ :=
      ⟨hyIntA, hyNotClB⟩
    exact
      (interior_maximal hO_subset hO_open) hz_mem
  -- Supply the required witness in `U ∩ interior (A \ closure B)`.
  exact ⟨y, ⟨hyU, hyIntDiff⟩⟩

theorem semi_open_inter_open_inter {A B C : Set X} (hA : SemiOpen A) (hB : IsOpen B) (hC : IsOpen C) : SemiOpen (A ∩ (B ∩ C)) := by
  -- The intersection `B ∩ C` is open.
  have hBC_open : IsOpen (B ∩ C) := hB.inter hC
  -- Intersect the (open) set `B ∩ C` with the semi-open set `A`.
  have hSemi : SemiOpen ((B ∩ C) ∩ A) :=
    open_intersection_semi_open_is_semi_open hBC_open hA
  -- Re-associate and commute to match the desired shape.
  simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using hSemi

theorem union_of_alpha_open_and_open_is_alpha_open {A B : Set X} (hA : AlphaOpen A) (hB : IsOpen B) : AlphaOpen (A ∪ B) := by
  -- Unfold the definition of `AlphaOpen`.
  intro x hx
  -- Analyse the two possibilities given by `hx : x ∈ A ∪ B`.
  cases hx with
  | inl hxA =>
      ------------------------------------------------------------
      -- Case 1 :  `x ∈ A`
      ------------------------------------------------------------
      -- From the α–openness of `A` we have
      have hA_int : x ∈ interior (closure (interior A)) := hA hxA
      -- Relate the two closures appearing in the goal.
      have h_closure_subset :
          (closure (interior A) : Set X) ⊆
            closure (interior (A ∪ B)) := by
        -- First compare the interiors.
        have h_int :
            (interior A : Set X) ⊆ interior (A ∪ B) := by
          -- Because `A ⊆ A ∪ B`.
          have h_sub : (A : Set X) ⊆ A ∪ B := by
            intro y hy; exact Or.inl hy
          exact interior_mono h_sub
        -- Taking closures preserves inclusion.
        exact closure_mono h_int
      -- Monotonicity of `interior`.
      have h_int_subset :
          (interior (closure (interior A)) : Set X) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono h_closure_subset
      -- Conclude for this case.
      exact h_int_subset hA_int
  | inr hxB =>
      -----------------------------------------------------------
      -- Case 2 :  `x ∈ B`
      -----------------------------------------------------------
      -- Since `B` is open we will first show that `x` belongs to
      -- `interior (A ∪ B)`, and then move on to the required set.
      have hB_open : IsOpen (B : Set X) := hB
      -- `B ⊆ interior (A ∪ B)` because `B` is open and
      -- contained in `A ∪ B`.
      have hB_to_int :
          (B : Set X) ⊆ interior (A ∪ B) := by
        have h_sub : (B : Set X) ⊆ (A ∪ B) := by
          intro y hy; exact Or.inr hy
        exact interior_maximal h_sub hB_open
      -- Hence `x ∈ interior (A ∪ B)`.
      have hx_int : x ∈ interior (A ∪ B) := hB_to_int hxB
      -- Show that `interior (A ∪ B)` is contained in the desired
      -- interior via maximality.
      have h_int_subset :
          (interior (A ∪ B) : Set X) ⊆
            interior (closure (interior (A ∪ B))) := by
        -- `interior (A ∪ B)` is open and clearly contained in its
        -- own closure.
        have h_open : IsOpen (interior (A ∪ B)) := isOpen_interior
        have h_sub :
            (interior (A ∪ B) : Set X) ⊆
              closure (interior (A ∪ B)) := by
          intro y hy; exact subset_closure hy
        exact interior_maximal h_sub h_open
      -- Apply the inclusion to finish.
      exact h_int_subset hx_int

theorem dense_union_alpha_open_interior_is_dense {A B : Set X} (hA : Dense A) (hB : AlphaOpen (interior B)) : Dense (A ∪ B) := by
  dsimp [Dense] at hA ⊢
  simp [closure_union, hA, Set.univ_union]

theorem dense_random_union {A B : Set X} (hA : Dense A) : Dense (A ∪ interior B) := by
  simpa using
    (dense_union_with_open_is_dense (A := A) (B := interior B) hA isOpen_interior)

theorem alpha_open_union_preopen_intersection {A B : Set X} (hA : AlphaOpen A) (hB : PreOpen B) : AlphaOpen (A ∪ (A ∩ B)) := by
  have hEq : (A ∪ (A ∩ B) : Set X) = A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hA => exact hA
      | inr hAB => exact hAB.1
    · intro hx
      exact Or.inl hx
  simpa [hEq] using hA

theorem intersection_alpha_open_dense_of_dense {A B C : Set X} (hA : AlphaOpen A) (hB : Dense B) (hC : Dense C) : PreOpen (A ∩ (B ∪ C)) := by
  have hBC : Dense (B ∪ C) := union_of_dense_sets_is_dense hB hC
  simpa using
    (dense_intersections_alpha_open_is_preopen (A := A) (B := B ∪ C) hA hBC)

theorem interior_alpha_open_intersection_of_dense {A B : Set X} (hA : AlphaOpen A) (hB : Dense B) : AlphaOpen (interior (A ∩ B)) := by
  simpa using
    (open_set_is_alpha_open (A := interior (A ∩ B)) isOpen_interior)

theorem dense_union_alpha_open_and_dense_is_dense {A B : Set X} (hA : AlphaOpen A) (hB : Dense B) : Dense (A ∪ closure B) := by
  dsimp [Dense] at hB ⊢
  simpa [closure_union, closure_closure, hB, Set.union_univ, Set.univ_union]

theorem semi_open_interior_is_alpha_open_if_dense {A : Set X} (h : Dense A) : AlphaOpen (interior A) := by
  intro x hx
  -- `interior A` is an open neighbourhood of `x`.
  have h_nhds : (interior A : Set X) ∈ 𝓝 x :=
    IsOpen.mem_nhds isOpen_interior hx
  -- Hence its closure is also a neighbourhood of `x`.
  have h_cl_nhds : (closure (interior A) : Set X) ∈ 𝓝 x :=
    Filter.mem_of_superset h_nhds subset_closure
  -- Therefore `x` belongs to the interior of this closure.
  have h_mem : x ∈ interior (closure (interior A)) :=
    (mem_interior_iff_mem_nhds).2 h_cl_nhds
  -- Rewriting finishes the proof.
  simpa [interior_interior] using h_mem

theorem semi_open_union_of_dense_closure_is_dense {A B : Set X} (hA : Dense A) (hB : SemiOpen (closure B)) : Dense (A ∪ B) := by
  simpa [Set.union_comm] using
    (union_of_semi_open_closure_and_dense_is_dense (A := B) (B := A) hB hA)

theorem preopen_closure_iff_open_closure {A : Set X} : PreOpen (closure A) ↔ IsOpen (closure A) := by
  -- `PreOpen` is an inclusion relation; unfold it.
  constructor
  · intro hPre
    -- Unfold in the hypothesis.
    dsimp [PreOpen] at hPre
    -- Use `closure_closure` to remove the redundant closure.
    have hsubset : (closure A : Set X) ⊆ interior (closure A) := by
      simpa [closure_closure] using hPre
    -- We always have `interior (closure A) ⊆ closure A`.
    -- Hence the two sets coincide.
    have h_eq : interior (closure A) = closure A :=
      Set.Subset.antisymm interior_subset hsubset
    -- The interior of any set is open; rewrite via the equality.
    have : IsOpen (interior (closure A)) := isOpen_interior
    simpa [h_eq] using this
  · intro hOpen
    -- We must show the defining inclusion for `PreOpen`.
    dsimp [PreOpen]
    -- For an open set, its interior is itself.
    have h_eq : interior (closure A) = closure A := hOpen.interior_eq
    -- The required inclusion is now trivial.
    have hsubset : (closure A : Set X) ⊆ interior (closure A) := by
      simpa [h_eq] using (Set.Subset.refl (closure A))
    -- Undo the earlier simplification with `closure_closure`.
    simpa [closure_closure] using hsubset

theorem preopen_union_interior_alpha_open {A B : Set X} (hA : PreOpen A) (hB : AlphaOpen B) : PreOpen (A ∪ interior B) := by
  -- `interior B` is open, hence α-open.
  have hIntB_alpha : AlphaOpen (interior B) := by
    simpa using
      open_set_is_alpha_open (A := interior B) isOpen_interior
  -- Apply the lemma for the union of an α-open and a preopen set
  -- and rewrite the union.
  simpa [Set.union_comm] using
    (union_of_alpha_open_and_preopen_is_preopen hIntB_alpha hA)

theorem closure_of_semi_open_union_dense_is_preopen {A B : Set X} (hA : SemiOpen A) (hB : Dense B) : PreOpen (closure (A ∪ B)) := by
  -- Unfold the definition of `PreOpen`.
  dsimp [PreOpen]
  intro x hx
  -- Compute `closure (A ∪ B)` using the density of `B`.
  have h_closure_union : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : (closure (A ∪ B : Set X)) =
        closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using (closure_union (A := A) (B := B))
    simpa [hB.closure_eq, Set.univ_union] using this
  -- Turn the assumption `hx` into `x ∈ univ`.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    simpa [h_closure_union] using hx
  -- Rewriting the goal with the preceding equality finishes the proof.
  simpa [h_closure_union, closure_closure, interior_univ] using hx_univ

theorem dense_open_is_semi_open {A : Set X} (h : IsOpen A) (hd : Dense A) : SemiOpen A := by
  dsimp [SemiOpen]
  intro x hx
  -- since `A` is open, its interior is itself
  have hx_int : x ∈ interior (A : Set X) := by
    simpa [h.interior_eq] using hx
  -- every point of `interior A` is in its closure
  exact subset_closure hx_int

theorem alpha_open_of_dense_and_semi_open {A : Set X} (hA : Dense A) (hB : SemiOpen A) : AlphaOpen A := by
  -- Expand the definitions of the two hypotheses.
  dsimp [AlphaOpen, SemiOpen] at *
  -- Take an arbitrary point `x ∈ A`.
  intro x hxA
  ------------------------------------------------------------------
  -- Step 1.  Show that `closure (interior A) = univ`.
  ------------------------------------------------------------------
  have h_closureInt_eq_univ : (closure (interior (A : Set X))) =
      (Set.univ : Set X) := by
    -- From semi-openness we have `A ⊆ closure (interior A)`.
    have h_sub : (A : Set X) ⊆ closure (interior (A : Set X)) := hB
    -- Taking closures preserves inclusion.
    have h_closure_sub :
        (closure (A : Set X)) ⊆ closure (closure (interior (A : Set X))) :=
      closure_mono h_sub
    -- Remove the redundant closure on the right.
    have h_closure_sub' :
        (closure (A : Set X)) ⊆ closure (interior (A : Set X)) := by
      simpa [closure_closure] using h_closure_sub
    -- Because `A` is dense, `closure A = univ`.
    have h_closureA_univ :
        (closure (A : Set X)) = (Set.univ : Set X) := hA.closure_eq
    -- Hence `univ ⊆ closure (interior A)`.
    have h_univ_subset :
        (Set.univ : Set X) ⊆ closure (interior (A : Set X)) := by
      simpa [h_closureA_univ] using h_closure_sub'
    -- Combine the two inclusions to obtain the desired equality.
    apply Set.Subset.antisymm
    · intro y _; trivial
    · exact h_univ_subset
  ------------------------------------------------------------------
  -- Step 2.  Compute the relevant interior.
  ------------------------------------------------------------------
  have h_int_eq_univ :
      interior (closure (interior (A : Set X))) =
        (Set.univ : Set X) := by
    simpa [h_closureInt_eq_univ, interior_univ]
  ------------------------------------------------------------------
  -- Step 3.  Conclude that `x` belongs to the required interior.
  ------------------------------------------------------------------
  simpa [h_int_eq_univ] using (Set.mem_univ x)

theorem dense_union_closure_is_preopen_if_open {A B : Set X} (hA : Dense A) (hB : IsOpen B) : PreOpen (A ∪ closure B) := by
  dsimp [PreOpen]
  intro x hx
  -- `A` is dense, hence `closure A = univ`.
  have hA_closure : (closure (A : Set X)) = (Set.univ : Set X) := hA.closure_eq
  -- Compute `closure (A ∪ closure B)`.
  have h_closure_union :
      closure (A ∪ closure B : Set X) = (Set.univ : Set X) := by
    calc
      closure (A ∪ closure B : Set X)
          = closure A ∪ closure (closure B) := by
            simpa using closure_union (A) (closure B)
      _ = closure A ∪ closure B := by
            simpa [closure_closure]
      _ = (Set.univ : Set X) := by
            simpa [hA_closure, Set.univ_union]
  -- Trivially, any point belongs to `univ`.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    trivial
  -- Rewrite the goal using `h_closure_union`.
  simpa [h_closure_union, interior_univ] using hx_univ

theorem alpha_open_disjoint_union {A B : Set X} (hA : AlphaOpen A) (hB : AlphaOpen B) : Disjoint A B → AlphaOpen (A ∪ B) := by
  intro _hdisj
  -- Expand the definition of `AlphaOpen`.
  dsimp [AlphaOpen] at hA hB ⊢
  -- Take an arbitrary point in `A ∪ B`.
  intro x hx
  -- Analyse the two alternatives for `x`.
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hA_int : x ∈ interior (closure (interior A)) := hA hxA
      -- `interior A ⊆ interior (A ∪ B)`
      have h_int_subset : (interior A : Set X) ⊆ interior (A ∪ B) := by
        have h_open : IsOpen (interior A) := isOpen_interior
        have h_sub  : (interior A : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inl (interior_subset hy)
        exact interior_maximal h_sub h_open
      -- Hence, after taking closures and interiors,
      --   `interior (closure (interior A)) ⊆ interior (closure (interior (A ∪ B)))`.
      have h_int_subset' :
          (interior (closure (interior A)) : Set X) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono (closure_mono h_int_subset)
      exact h_int_subset' hA_int
  | inr hxB =>
      -- `x ∈ B`
      have hB_int : x ∈ interior (closure (interior B)) := hB hxB
      -- `interior B ⊆ interior (A ∪ B)`
      have h_int_subset : (interior B : Set X) ⊆ interior (A ∪ B) := by
        have h_open : IsOpen (interior B) := isOpen_interior
        have h_sub  : (interior B : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inr (interior_subset hy)
        exact interior_maximal h_sub h_open
      -- As before, lift the inclusion through closures and interiors.
      have h_int_subset' :
          (interior (closure (interior B)) : Set X) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono (closure_mono h_int_subset)
      exact h_int_subset' hB_int

theorem semi_open_of_preopen_and_open {A : Set X} (hA : PreOpen A) (hB : IsOpen A) : SemiOpen A := by
  -- Unfold the definition of `SemiOpen`.
  dsimp [SemiOpen] at *
  intro x hx
  -- Any point of `A` is contained in `closure A`.
  have hx_closureA : x ∈ closure (A : Set X) := subset_closure hx
  -- Since `A` is open, `interior A = A`, hence the two closures coincide.
  have h_cl_eq : (closure (interior (A : Set X)) : Set X) = closure A := by
    simpa [hB.interior_eq]
  -- Rewrite and conclude.
  simpa [h_cl_eq] using hx_closureA

theorem dense_complement_open_is_dense {A B : Set X} (hA : Dense A) (hB : IsOpen B) : Dense (A ∪ Bᶜ) := by
  dsimp [Dense] at hA ⊢
  simp [closure_union, hA]

theorem dense_union_inter_open_is_preopen {A B C : Set X} (hA : Dense A) (hB : IsOpen B) (hC : IsOpen C) : PreOpen (A ∪ (B ∩ C)) := by
  -- Unfold the definition of `PreOpen`.
  dsimp [PreOpen]
  intro x hx
  -- Because `A` is dense we have `closure A = univ`.
  have hA_closure : (closure (A : Set X)) = (Set.univ : Set X) := hA.closure_eq
  -- Hence the closure of `A ∪ (B ∩ C)` is also `univ`.
  have h_closure_union :
      (closure (A ∪ (B ∩ C) : Set X)) = (Set.univ : Set X) := by
    have : closure (A ∪ (B ∩ C) : Set X) =
        closure (A : Set X) ∪ closure (B ∩ C : Set X) := by
      simpa using closure_union (A := A) (B := B ∩ C)
    simpa [hA_closure, Set.univ_union] using this
  -- Trivially, any point belongs to `univ`.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  -- Rewriting with `h_closure_union` gives the desired membership.
  simpa [h_closure_union, interior_univ] using this

theorem alpha_open_from_intersection_and_union {A B : Set X} (hA : AlphaOpen A) (hB : AlphaOpen B) : AlphaOpen (A ∩ (A ∪ B)) := by
  -- First simplify the set expression `A ∩ (A ∪ B)` to `A`.
  have hEq : (A ∩ (A ∪ B) : Set X) = A := by
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      exact ⟨hx, Or.inl hx⟩
  -- Rewrite and finish using the given hypothesis `hA : AlphaOpen A`.
  simpa [hEq] using hA

theorem closure_of_dense_and_alpha_open_is_dense {A B : Set X} (h₁ : Dense A) (h₂ : AlphaOpen B) : Dense (closure (A ∪ B)) := by
  dsimp [Dense] at h₁ ⊢
  simp [closure_closure, closure_union, h₁, Set.univ_union]

theorem dense_set_is_alpha_open_if_closed {A : Set X} (h : Dense A) (hc : IsClosed A) : AlphaOpen A := by
  -- Unfold the definition of `AlphaOpen`.
  dsimp [AlphaOpen]
  intro x hx
  -- Since `A` is closed and dense, we have `closure A = univ` and
  -- `closure A = A`, hence `A = univ`.
  have hAuniv : (A : Set X) = (Set.univ : Set X) := by
    simpa [hc.closure_eq] using h.closure_eq
  -- Membership in `univ` is trivial; rewrite the goal accordingly.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [hAuniv, interior_univ, closure_univ] using this

theorem open_is_preopen {A : Set X} (h : IsOpen A) : PreOpen A := by
  dsimp [PreOpen]
  intro x hx
  have h_nhds : (A : Set X) ∈ 𝓝 x := h.mem_nhds hx
  have h_cl_nhds : (closure A : Set X) ∈ 𝓝 x :=
    Filter.mem_of_superset h_nhds subset_closure
  exact (mem_interior_iff_mem_nhds).2 h_cl_nhds

theorem pre_open_interior {A : Set X} (h : PreOpen A) : PreOpen (interior A) := by
  -- `interior A` is open and contained in its closure
  intro x hx
  have h_sub :
      (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal (by
      intro y hy
      exact subset_closure hy) isOpen_interior
  exact h_sub hx

theorem dense_semi_open_intersection {B : Set X} (h : Dense B) : SemiOpen (B ∩ interior B) := by
  -- Since `interior B ⊆ B`, their intersection is just `interior B`.
  have h_eq : (B ∩ interior (B : Set X) : Set X) = interior B := by
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨interior_subset hx, hx⟩
  -- `interior B` is semi-open because `B` is dense.
  have h_semi : SemiOpen (interior B) := semi_open_interior_of_dense (A := B) h
  -- Transport the result through the above equality.
  simpa [h_eq] using h_semi

theorem alpha_preopen_union_dense {A : Set X} (h : AlphaOpen A) : ∃ B, PreOpen B ∧ Dense (A ∪ B) := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · -- `PreOpen` for `univ`
    dsimp [PreOpen]
    intro x hx
    simpa [closure_univ, interior_univ] using hx
  · -- `Dense` for `A ∪ univ`
    dsimp [Dense]
    simp [Set.union_univ]

theorem preopen_intersection_of_open_and_dense {A B : Set X} (hA : IsOpen A) (hB : Dense B) : PreOpen (A ∩ B) := by
  simpa [Set.inter_comm] using
    (dense_intersection_is_preopen_if_open (A := B) (B := A) hB hA)

theorem empty_alpha_open_union {A : Set X} (h : AlphaOpen A) : AlphaOpen (∅ ∪ A) := by
  simpa [Set.empty_union] using h

theorem finite_inter_union_alpha_open {I : Type*} [Finite I] {f : I → Set X} (h : ∀ i, AlphaOpen (f i)) : AlphaOpen (⋂ i, f i) := by
  simpa using
    (finite_intersection_of_alpha_open_sets_is_alpha_open (I := I) (f := f) h)

theorem preopen_union_interior_closure_is_preopen {A B : Set X} (hA : PreOpen A) : PreOpen (A ∪ interior (closure B)) := by
  -- First, `interior (closure B)` is an open set.
  have h_open : IsOpen (interior (closure (B : Set X))) := isOpen_interior
  -- Apply the lemma for the union of an open and a preopen set, with
  -- the roles of the sets swapped.
  have h_pre : PreOpen (interior (closure (B : Set X)) ∪ A) :=
    open_union_preopen_is_preopen (A := interior (closure B)) (B := A) h_open hA
  -- Rewrite the union to match the required order.
  simpa [Set.union_comm] using h_pre

theorem closure_of_preopen_union_closure_is_preopen {A B : Set X} (hA : PreOpen A) (hB : Dense B) : PreOpen (closure (A ∪ closure B)) := by
  -- First, compute the closure of `A ∪ closure B`.
  have h_closure : (closure (A ∪ closure (B : Set X) : Set X)) =
      (Set.univ : Set X) := by
    have : (closure (A ∪ closure (B : Set X) : Set X)) =
        closure (A : Set X) ∪ closure (closure (B : Set X)) := by
      simpa using closure_union (A := A) (B := closure B)
    simpa [hB.closure_eq, closure_closure, Set.univ_union] using this
  -- `univ` is open, hence preopen.
  simpa [h_closure] using
    (open_is_preopen (A := (Set.univ : Set X)) isOpen_univ)

theorem intersection_of_preopen_and_alpha_open_is_preopen {A B : Set X} (hA : PreOpen A) (hB : AlphaOpen B) : PreOpen (A ∩ B) := by
  simpa [Set.inter_comm] using
    (preopen_intersection_of_alpha_open (A := B) (B := A) hB hA)

theorem preopen_union_of_dense_sets {A B : Set X} (hA : Dense A) (hB : Dense B) : PreOpen (A ∪ B) := by
  dsimp [PreOpen]
  intro x hx
  -- The closures of the dense sets are `univ`, hence so is the closure of their union.
  have h_closure_union : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : (closure (A ∪ B : Set X)) =
        closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using closure_union (A := A) (B := B)
    simpa [hA.closure_eq, hB.closure_eq, Set.union_univ] using this
  -- Membership is now trivial.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_closure_union, interior_univ] using this

theorem open_set_union_semi_open_subset {A B : Set X} (hA : IsOpen A) (hB : SemiOpen B) : A ⊆ closure (A ∪ B) := by
  intro x hx
  exact subset_closure (Or.inl hx)

theorem alpha_open_and_dense_closure_is_dense {A B : Set X} (hA : AlphaOpen A) (hB : Dense (closure B)) : Dense (A ∪ B) := by
  -- use `hA` so that it is not treated as an unused hypothesis
  have _ := hA
  -- Expand `Dense` in the hypothesis and in the goal
  dsimp [Dense] at hB ⊢
  -- Fix an arbitrary point `x`
  intro x
  -- From `hB` we know that every point is in `closure B`
  have hxB : x ∈ closure (B : Set X) := by
    -- `hB` is a statement about `closure B`, remove the redundant closure
    simpa [closure_closure] using hB x
  -- Since `B ⊆ A ∪ B`, we have `closure B ⊆ closure (A ∪ B)`
  have h_sub : (closure (B : Set X)) ⊆ closure (A ∪ B) := by
    apply closure_mono
    intro y hy
    exact Or.inr hy
  -- Conclude that `x ∈ closure (A ∪ B)`
  exact h_sub hxB

theorem dense_patch_alpha_open {A B : Set X} (hA : Dense A) (hB : AlphaOpen B) : SemiOpen (closure (A ∪ B)) := by
  -- Unfold `SemiOpen`.
  dsimp [SemiOpen]
  intro x hx
  -- Compute `closure (A ∪ B)` using the density of `A`.
  have h_closure_union : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : (closure (A ∪ B : Set X)) =
        closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using (closure_union (A := A) (B := B))
    simpa [hA.closure_eq, Set.univ_union] using this
  -- Rewrite `hx` with the previous equality.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    simpa [h_closure_union] using hx
  -- Rewriting the goal yields a trivial statement.
  simpa [h_closure_union, interior_univ, closure_univ] using hx_univ

theorem semi_open_and_dense_union {A B : Set X} (hA : SemiOpen A) (hB : Dense B) : SemiOpen (closure (A ∪ B)) := by
  dsimp [SemiOpen]
  intro x hx
  -- Using the density of `B`, compute the closure of `A ∪ B`.
  have h_closure_union : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : (closure (A ∪ B : Set X)) =
        closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using (closure_union (A := A) (B := B))
    simpa [hB.closure_eq, Set.union_univ] using this
  -- Transport the hypothesis through the above equality.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    simpa [h_closure_union] using hx
  -- Rewriting the goal with the computed closure finishes the proof.
  simpa [h_closure_union, interior_univ, closure_univ] using hx_univ

theorem intersection_dense_subset_alpha_open {A : Set X} (h : Dense A) : ∀ B, AlphaOpen B → A ∩ B ⊆ closure (interior B) := by
  intro B hB
  -- absorb the density hypothesis so it is used
  have _ := h
  intro x hx
  -- `x` lies in `B`
  have hxB : x ∈ B := hx.2
  -- α-openness of `B` gives the interior membership
  have hx_int : x ∈ interior (closure (interior B)) := hB hxB
  -- the required closure contains this interior
  exact
    (interior_subset : interior (closure (interior B)) ⊆ closure (interior B))
      hx_int

theorem intersection_with_self_is_preopen {A : Set X} (h : PreOpen A) : PreOpen (A ∩ A) := by
  dsimp [PreOpen] at h ⊢
  simpa [Set.inter_self] using h

theorem preopen_intersection_empty {A : Set X} : PreOpen (A ∩ ∅) := by
  dsimp [PreOpen]
  intro x hx
  cases hx.2

theorem alpha_open_empty_set : AlphaOpen (∅ : Set X) := by
  dsimp [AlphaOpen]
  exact Set.empty_subset _

theorem dense_set_union_empty {A : Set X} (hA : Dense A) : Dense (A ∪ ∅) := by
  dsimp [Dense] at hA ⊢
  simpa [Set.union_empty] using hA

theorem open_set_union_empty {A : Set X} (hA : IsOpen A) : IsOpen (A ∪ ∅) := by
  simpa [Set.union_empty] using hA

theorem dense_set_union_universal {A : Set X} (hA : Dense A) : Dense (A ∪ Set.univ) := by
  dsimp [Dense]
  simp [Set.union_univ, closure_univ]

theorem semi_open_universal_set : SemiOpen (Set.univ : Set X) := by
  simpa [SemiOpen, interior_univ, closure_univ]

theorem alpha_open_union_self_is_alpha_open {A : Set X} (hA : AlphaOpen A) : AlphaOpen (A ∪ A) := by
  simpa [Set.union_self] using hA

theorem sem_open_if_union_of_semi_open (A B : Set X) (hA : SemiOpen A) (hB : SemiOpen B) : SemiOpen (A ∪ B) := by
  -- Unfold `SemiOpen` in the hypotheses and goal.
  dsimp [SemiOpen] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hx_clA : x ∈ closure (interior A) := hA hxA
      -- `interior A ⊆ interior (A ∪ B)`
      have h_sub_int : (interior A : Set X) ⊆ interior (A ∪ B) := by
        have h_sub : (A : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact interior_mono h_sub
      -- Passing to closures
      have h_sub_cl :
          (closure (interior A) : Set X) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_sub_int
      exact h_sub_cl hx_clA
  | inr hxB =>
      -- `x ∈ B`
      have hx_clB : x ∈ closure (interior B) := hB hxB
      -- `interior B ⊆ interior (A ∪ B)`
      have h_sub_int : (interior B : Set X) ⊆ interior (A ∪ B) := by
        have h_sub : (B : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inr hy
        exact interior_mono h_sub
      -- Passing to closures
      have h_sub_cl :
          (closure (interior B) : Set X) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_sub_int
      exact h_sub_cl hx_clB

theorem open_set_inter_disjoint_is_semi_open {A B : Set X} (hA : IsOpen A) (hB : Disjoint A B) : SemiOpen (A ∩ B) := by
  -- Because `A` and `B` are disjoint, their intersection is empty.
  have hEq : (A ∩ B : Set X) = (∅ : Set X) := by
    simpa using (Set.disjoint_iff_inter_eq_empty).1 hB
  -- The empty set is semi-open.
  have h_empty : SemiOpen (∅ : Set X) := by
    dsimp [SemiOpen]
    intro x hx
    cases hx
  -- Transport the result through the established equality.
  simpa [hEq] using h_empty

theorem dense_set_union_closure_of_preopen {A B : Set X} (hA : Dense A) (hB : PreOpen (closure B)) : Dense (A ∪ closure B) := by
  dsimp [Dense] at hA ⊢
  simpa [closure_union, closure_closure, hA, Set.univ_union]

theorem alpha_open_intersection_with_dense_union {A B : Set X} (hA : AlphaOpen A) (hB : Dense B) : AlphaOpen (A ∩ closure (A ∪ B)) := by
  -- Since `B` is dense, `closure B = univ`, hence
  -- `closure (A ∪ B) = closure A ∪ univ = univ`.
  have h_closure : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : (closure (A ∪ B : Set X)) =
        closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using closure_union (A := A) (B := B)
    simpa [hB.closure_eq, Set.union_univ] using this
  -- Rewriting with `h_closure` turns the goal into `AlphaOpen A`,
  -- which is exactly `hA`.
  simpa [h_closure] using hA

theorem semi_open_intersection_with_dense_union {A B : Set X} (hA : SemiOpen A) (hB : Dense B) : SemiOpen (A ∩ closure (A ∪ B)) := by
  -- First, compute `closure (A ∪ B)` using the density of `B`.
  have h_closure : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : (closure (A ∪ B : Set X)) =
        closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using closure_union (A := A) (B := B)
    simpa [hB.closure_eq, Set.union_univ] using this
  -- Rewriting turns the goal into `SemiOpen A`, which is given by `hA`.
  simpa [h_closure, Set.inter_univ] using hA

theorem preopen_union_of_dense_closure_and_open {A B : Set X} (hA : Dense (closure A)) (hB : IsOpen B) : PreOpen (A ∪ B) := by
  dsimp [PreOpen]
  intro x hx
  -- Compute `closure A` using its density.
  have h_closureA : (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa [closure_closure] using hA.closure_eq
  -- Compute `closure (A ∪ B)`; it is the whole space as well.
  have h_closure_union : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : (closure (A ∪ B : Set X)) =
        closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using (closure_union (A := A) (B := B))
    simpa [h_closureA, Set.univ_union] using this
  -- (Optionally) register the openness of `B` so the hypothesis is used.
  have _ := hB
  -- Membership in `univ` is trivial.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  -- Rewriting with the computed closure finishes the proof.
  simpa [h_closure_union, interior_univ] using this

theorem closure_of_dense_preopen_union {A B : Set X} (hA : Dense A) (hB : PreOpen B) : PreOpen (closure (A ∪ B)) := by
  dsimp [PreOpen] at *
  intro x hx
  -- Use `hB` so it is not treated as unused.
  have _ := hB
  ----------------------------------------------------------------
  -- Compute the closure of `A ∪ B` using the density of `A`.
  ----------------------------------------------------------------
  have h_closure_union :
      (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : (closure (A ∪ B : Set X)) =
        closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using (closure_union (A := A) (B := B))
    simpa [hA.closure_eq, Set.univ_union] using this
  ----------------------------------------------------------------
  -- Transport `hx : x ∈ closure (A ∪ B)` through the above equality.
  ----------------------------------------------------------------
  have hx_univ : x ∈ (Set.univ : Set X) := by
    simpa [h_closure_union] using (hx : x ∈ closure (A ∪ B : Set X))
  ----------------------------------------------------------------
  -- Rewriting gives the desired membership in the required interior.
  ----------------------------------------------------------------
  simpa [h_closure_union, closure_closure, interior_univ] using hx_univ

theorem semi_open_closure_of_alpha_open_union {A B : Set X} (hA : AlphaOpen A) (hB : AlphaOpen B) : SemiOpen (closure (A ∪ B)) := by
  have hA_semi : SemiOpen A := alpha_open_implies_semi_open hA
  exact closure_of_semi_open_union_alpha_open hA_semi hB

theorem closure_semi_open_inter_open_is_semi_open {A B : Set X} (hA : SemiOpen A) (hB : IsOpen B) : SemiOpen (closure (A ∩ B)) := by
  -- First, `A ∩ B` is semi-open because `B` is open and `A` is semi-open.
  have h_inter : SemiOpen (A ∩ B) := by
    simpa [Set.inter_comm] using
      (open_intersection_semi_open_is_semi_open (A := B) (B := A) hB hA)
  -- The closure of a semi-open set is semi-open.
  simpa using (closure_semi_open (A := A ∩ B) h_inter)

theorem preopen_subspace_of_dense_union {A B : Set X} (hA : Dense A) (hB : Dense B) : PreOpen (closure (A ∪ B)) := by
  -- Unfold `PreOpen`.
  dsimp [PreOpen]
  intro x hx
  -- Compute `closure (A ∪ B)` using the density of `A` and `B`.
  have h_closure_union : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : closure (A ∪ B : Set X) =
        closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using (closure_union (A := A) (B := B))
    simpa [hA.closure_eq, hB.closure_eq, Set.union_univ] using this
  -- Transport `hx : x ∈ closure (A ∪ B)` through the above equality.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    simpa [h_closure_union] using hx
  -- Rewriting with `h_closure_union` gives the desired membership.
  simpa [h_closure_union, closure_closure, interior_univ] using hx_univ

theorem preopen_set_is_semi_open_if_open {A : Set X} (h : IsOpen A) : SemiOpen A := by
  dsimp [SemiOpen]
  intro x hx
  have hx_cl : x ∈ closure (A : Set X) := subset_closure hx
  simpa [h.interior_eq] using hx_cl

theorem union_of_finite_alpha_open_sets_is_alpha_open {A B : Set X} (hA : AlphaOpen A) (hB : AlphaOpen B) : AlphaOpen (A ∪ B) := by
  -- Unfold the definition of `AlphaOpen`.
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hA_int : x ∈ interior (closure (interior A)) := hA hxA
      -- `interior A ⊆ interior (A ∪ B)`
      have h_int_sub : (interior A : Set X) ⊆ interior (A ∪ B) := by
        have h_sub : (A : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact interior_mono h_sub
      -- Passing to closures and then interiors gives the desired inclusion.
      have h_incl :
          (interior (closure (interior A)) : Set X) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono (closure_mono h_int_sub)
      exact h_incl hA_int
  | inr hxB =>
      -- `x ∈ B`
      have hB_int : x ∈ interior (closure (interior B)) := hB hxB
      -- `interior B ⊆ interior (A ∪ B)`
      have h_int_sub : (interior B : Set X) ⊆ interior (A ∪ B) := by
        have h_sub : (B : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inr hy
        exact interior_mono h_sub
      -- As above, obtain the required inclusion.
      have h_incl :
          (interior (closure (interior B)) : Set X) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono (closure_mono h_int_sub)
      exact h_incl hB_int

theorem finite_union_of_alpha_open_sets_is_semi_open {A B : Set X} (hA : AlphaOpen A) (hB : AlphaOpen B) : SemiOpen (A ∪ B) := by
  -- First, `A ∪ B` is α-open as the union of two α-open sets.
  have hAlpha : AlphaOpen (A ∪ B) :=
    union_of_finite_alpha_open_sets_is_alpha_open hA hB
  -- Every α-open set is semi-open.
  exact alpha_open_implies_semi_open hAlpha

theorem dense_and_polyhedral_union_is_dense {A B : Set X} (hA : Dense A) (hB : PreOpen B) : Dense (A ∪ closure B) := by
  dsimp [Dense] at hA ⊢
  -- consume `hB` so it is not marked as unused
  have _ := hB
  simpa [closure_union, closure_closure, hA, Set.univ_union]

theorem closure_of_union_of_alpha_open_and_dense_is_alpha_open {A B : Set X} (hA : AlphaOpen A) (hB : Dense B) : AlphaOpen (closure (A ∪ B)) := by
  simpa [Set.union_comm] using
    (closure_of_dense_union_is_alpha_open (A := B) (B := A) hB hA)

theorem preopen_of_union_alpha_open {A B : Set X} (hA : AlphaOpen A) : PreOpen (A ∪ interior B) := by
  -- `interior B` is open, hence preopen.
  have hInt_pre : PreOpen (interior B) :=
    open_is_preopen (A := interior B) isOpen_interior
  -- Apply the lemma for the union of an α-open and a preopen set.
  simpa using
    (union_of_alpha_open_and_preopen_is_preopen (A := A) (B := interior B) hA hInt_pre)

theorem preopen_union_semi_open_dense {A B : Set X} (hA : SemiOpen A) (hB : Dense B) : PreOpen (A ∪ closure B) := by
  dsimp [PreOpen] at *
  intro x hx
  -- consume `hx` to avoid unused-variable warning
  have _ := hx
  -- `B` is dense, so its closure is the whole space
  have h_closureB : (closure (B : Set X)) = (Set.univ : Set X) := hB.closure_eq
  -- hence the union is also the whole space
  have h_union : (A ∪ closure (B : Set X) : Set X) = (Set.univ : Set X) := by
    simpa [h_closureB, Set.union_univ]
  -- every point belongs to `univ`
  have : x ∈ (Set.univ : Set X) := by
    trivial
  -- rewrite the goal using the fact that the union is `univ`
  simpa [h_union, closure_univ, interior_univ] using this

theorem dense_closure_semi_open_union {A B : Set X} (hA : Dense A) (hB : SemiOpen B) : PreOpen (closure (A ∪ B)) := by
  -- Unfold `PreOpen`.
  dsimp [PreOpen]
  intro x hx
  -- Touch `hB` so it is not considered unused.
  have _ := hB
  -- Compute the closure of `A ∪ B` using the density of `A`.
  have h_closure_union :
      (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    calc
      closure (A ∪ B : Set X)
          = closure (A : Set X) ∪ closure (B : Set X) := by
            simpa using closure_union (A := A) (B := B)
      _ = (Set.univ : Set X) := by
            simpa [hA.closure_eq, Set.univ_union]
  -- Transport `hx` through the above equality.
  have : x ∈ (Set.univ : Set X) := by
    simpa [h_closure_union] using hx
  -- Rewriting the goal with the computed closure finishes the proof.
  simpa [h_closure_union, closure_closure, closure_univ, interior_univ] using this

theorem preopen_intersections_semi_open_interior {A B : Set X} (hA : PreOpen A) (hB : SemiOpen B) : PreOpen (interior (A ∩ B)) := by
  dsimp [PreOpen]
  intro x hx
  -- touch the hypotheses so they are not marked as unused
  have _ := hA
  have _ := hB
  -- `interior (A ∩ B)` is open and contained in its closure,
  -- hence contained in the interior of that closure
  have h_sub :
      (interior (A ∩ B) : Set X) ⊆
        interior (closure (interior (A ∩ B))) :=
    interior_maximal (by
      intro y hy
      exact subset_closure hy) isOpen_interior
  exact h_sub hx

theorem intersection_of_alpha_open_sets_is_semi_open {A B : Set X} (hA : AlphaOpen A) (hB : AlphaOpen B) : SemiOpen (A ∩ B) := by
  exact
    alpha_open_implies_semi_open
      (intersection_of_alpha_open_sets_is_alpha_open hA hB)

theorem dense_union_with_preopen_is_dense {A B : Set X} (hA : Dense A) (hB : PreOpen B) : Dense (A ∪ B) := by
  simpa [Set.union_comm] using
    (dense_preopen_union_is_dense (A := B) (B := A) hB hA)

theorem preopen_union_alpha_open_closure_is_preopen {A B : Set X} (hA : PreOpen A) (hB : AlphaOpen (closure B)) : PreOpen (A ∪ B) := by
  -- Unfold `PreOpen`.
  intro x hx
  cases hx with
  | inl hA_mem =>
      -- `x ∈ A`
      have hA_int : x ∈ interior (closure A) := hA hA_mem
      -- `closure A ⊆ closure (A ∪ B)`
      have h_sub : (closure A : Set X) ⊆ closure (A ∪ B) := by
        have h_sub' : (A : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact closure_mono h_sub'
      -- Monotonicity of `interior`
      exact (interior_mono h_sub) hA_int
  | inr hB_mem =>
      -- `x ∈ B`
      -- Regard `x` as a point of `closure B`.
      have hx_clB : x ∈ closure (B : Set X) := subset_closure hB_mem
      -- Use the α-openness of `closure B`.
      have hB_int :
          x ∈ interior (closure (interior (closure (B : Set X)))) :=
        hB hx_clB
      ----------------------------------------------------------------
      --  Build the required inclusion of the two closures.
      ----------------------------------------------------------------
      have h_sub :
          (closure (interior (closure (B : Set X))) : Set X) ⊆
            closure (A ∪ B) := by
        -- First link :
        --   `closure (interior (closure B)) ⊆ closure B`.
        have h₁ :
            (closure (interior (closure (B : Set X))) : Set X) ⊆
              closure (B : Set X) := by
          have h' :
              (interior (closure (B : Set X)) : Set X) ⊆
                closure (B : Set X) := interior_subset
          simpa [closure_closure] using (closure_mono h')
        -- Second link :
        --   `closure B ⊆ closure (A ∪ B)`.
        have h₂ :
            (closure (B : Set X)) ⊆ closure (A ∪ B) := by
          have h'' : (B : Set X) ⊆ A ∪ B := by
            intro y hy; exact Or.inr hy
          simpa using (closure_mono h'')
        -- Combine the two inclusions.
        exact Set.Subset.trans h₁ h₂
      -- Monotonicity of `interior` gives the desired membership.
      exact (interior_mono h_sub) hB_int

theorem concave_open_exists_closure_intersection {A B : Set X} (hA : IsOpen A) (hB : PreOpen B) : ∃ C, PreOpen C ∧ C ∩ closure B ⊆ A := by
  refine ⟨A, open_is_preopen hA, ?_⟩
  intro x hx
  exact hx.1

theorem union_semi_open_closure_alpha_open {A B : Set X} (hA : SemiOpen (closure A)) (hB : AlphaOpen B) : SemiOpen (closure (A ∪ B)) := by
  simpa [closure_union, closure_closure] using
    (closure_of_semi_open_union_alpha_open
        (A := closure (A)) (B := B) hA hB)

theorem dense_and_preopen_intersection_semi_open {A B : Set X} (hA : SemiOpen A) (hB : PreOpen B) : SemiOpen (closure (A ∪ B)) := by
  -- Unfold the definitions in the hypotheses and in the goal.
  dsimp [SemiOpen, PreOpen] at hA hB ⊢
  -- We will show  `closure (A ∪ B) ⊆ closure (interior (closure (A ∪ B)))`;
  -- the required statement is then obtained by applying this inclusion
  -- to the given point.
  have h_sub :
      (A ∪ B : Set X) ⊆ closure (interior (closure (A ∪ B))) := by
    intro y hy
    cases hy with
    | inl hyA =>
        -- `y ∈ A`
        -- Semi-openness of `A`
        have hA_cl : y ∈ closure (interior A) := hA hyA
        -- `interior A ⊆ interior (closure (A ∪ B))`
        have h_int :
            (interior A : Set X) ⊆ interior (closure (A ∪ B)) := by
          -- because `A ⊆ closure (A ∪ B)`
          have h_sub : (A : Set X) ⊆ closure (A ∪ B) := by
            intro z hz; exact subset_closure (Or.inl hz)
          exact interior_mono h_sub
        -- hence `closure (interior A) ⊆ closure (interior (closure (A ∪ B)))`
        have h_cl :
            (closure (interior A) : Set X) ⊆
              closure (interior (closure (A ∪ B))) :=
          closure_mono h_int
        exact h_cl hA_cl
    | inr hyB =>
        -- `y ∈ B`
        -- Pre-openness of `B`
        have hB_intCl : y ∈ interior (closure B) := hB hyB
        -- `interior (closure B) ⊆ interior (closure (A ∪ B))`
        have h_int :
            (interior (closure B) : Set X) ⊆
              interior (closure (A ∪ B)) := by
          -- because `closure B ⊆ closure (A ∪ B)`
          have h_sub : (closure B : Set X) ⊆ closure (A ∪ B) := by
            have : (B : Set X) ⊆ A ∪ B := by
              intro z hz; exact Or.inr hz
            exact closure_mono this
          exact interior_mono h_sub
        -- move from the interior to its closure
        have : y ∈ interior (closure (A ∪ B)) := h_int hB_intCl
        have h_to_cl :
            (interior (closure (A ∪ B)) : Set X) ⊆
              closure (interior (closure (A ∪ B))) := by
          intro z hz; exact subset_closure hz
        exact h_to_cl this
  -- The target on the right is closed.
  have h_closed : IsClosed (closure (interior (closure (A ∪ B)))) :=
    isClosed_closure
  -- Hence, by `closure_minimal`,
  have h_closure_subset :
      (closure (A ∪ B : Set X)) ⊆
        closure (interior (closure (A ∪ B))) :=
    closure_minimal h_sub h_closed
  -- Apply the inclusion to finish.
  intro x hx
  exact h_closure_subset hx

theorem preopen_if_closure_dense {A : Set X} (h : Dense (closure A)) : PreOpen A := by
  dsimp [PreOpen]
  intro x hx
  -- `h` tells us that `closure A` is dense, hence equal to `univ`.
  have h_closure_eq : (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa [closure_closure] using h.closure_eq
  -- Membership in `univ` is trivial.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  -- Rewriting with `h_closure_eq` completes the proof.
  simpa [h_closure_eq, interior_univ] using this

theorem interior_is_alpha_open_if_dense_supr_preopen {ι : Type*} [CompleteLattice ι] {f : ι → Set X} (h : ∀ i, PreOpen (f i)) : AlphaOpen (interior (⨆ i, f i)) := by
  -- consume the hypothesis so it is not marked as unused
  have _ := h
  simpa using
    (open_set_is_alpha_open (A := interior (⨆ i, f i : Set X)) isOpen_interior)

theorem preopen_if_dense_union_interior_is_preopen {A B : Set X} (hA : Dense A) (hB : PreOpen (interior B)) : PreOpen (interior (A ∪ B)) := by
  -- Use the hypotheses so that they are not marked as unused.
  have _ := hA
  have _ := hB
  -- `interior (A ∪ B)` is open, hence preopen.
  simpa using
    (open_is_preopen (A := interior (A ∪ B)) isOpen_interior)

theorem interior_union_semi_open_is_semi_open {A B : Set X} (h : SemiOpen A) : SemiOpen (interior (A ∪ B)) := by
  dsimp [SemiOpen] at h ⊢
  intro x hx
  -- keep `h` so it is not considered unused
  have _ := h
  simpa [interior_interior] using (subset_closure hx)

theorem alpha_open_union_closure_preopen_is_semi_open {A B : Set X} (hA : AlphaOpen A) (hB : PreOpen B) : SemiOpen (A ∪ closure B) := by
  -- Unfold the definition of `SemiOpen`.
  dsimp [SemiOpen]
  intro x hx
  -- Analyse whether `x` comes from `A` or from `closure B`.
  cases hx with
  | inl hxA =>
      ------------------------------------------------------------------
      -- Case 1 : `x ∈ A`
      ------------------------------------------------------------------
      -- α-openness of `A` gives the following interior membership.
      have h₁ : x ∈ interior (closure (interior A)) := hA hxA
      -- We will send this point to `closure (interior (A ∪ closure B))`.
      have h_subset :
          (interior (closure (interior A)) : Set X) ⊆
            closure (interior (A ∪ closure B)) := by
        -- First, relate the corresponding interiors.
        have h_int :
            (interior A : Set X) ⊆ interior (A ∪ closure B) := by
          have h_sub : (A : Set X) ⊆ A ∪ closure B := by
            intro y hy; exact Or.inl hy
          exact interior_mono h_sub
        -- Taking closures preserves inclusion.
        have h_cl :
            (closure (interior A) : Set X) ⊆
              closure (interior (A ∪ closure B)) :=
          closure_mono h_int
        -- Finally,
        exact Set.Subset.trans (interior_subset) h_cl
      exact h_subset h₁
  | inr hxClB =>
      ------------------------------------------------------------------
      -- Case 2 : `x ∈ closure B`
      ------------------------------------------------------------------
      -- We prove `x ∈ closure (interior (A ∪ closure B))`
      -- via the neighbourhood characterisation of the closure.
      have : x ∈ closure (interior (A ∪ closure B)) := by
        -- Use `mem_closure_iff`.
        apply (mem_closure_iff).2
        intro U hU hxU
        -- Because `x ∈ closure B`, the neighbourhood `U` meets `B`.
        have h_nonempty : ((U : Set X) ∩ B).Nonempty := by
          have := (mem_closure_iff).1 hxClB U hU hxU
          simpa [Set.inter_comm] using this
        rcases h_nonempty with ⟨y, ⟨hyU, hyB⟩⟩
        ----------------------------------------------------------------
        -- `y ∈ B`, and `B` is pre-open: `y ∈ interior (closure B)`.
        ----------------------------------------------------------------
        have hy_intClB : y ∈ interior (closure B) := hB hyB
        -- `interior (closure B)` sits inside `interior (A ∪ closure B)`.
        have h_incl :
            (interior (closure B) : Set X) ⊆ interior (A ∪ closure B) := by
          have h_sub : (closure B : Set X) ⊆ A ∪ closure B := by
            intro z hz; exact Or.inr hz
          exact interior_mono h_sub
        have hy_intUnion : y ∈ interior (A ∪ closure B) := h_incl hy_intClB
        -- Provide the required witness in `U ∩ interior (A ∪ closure B)`.
        exact ⟨y, ⟨hyU, hy_intUnion⟩⟩
      exact this

theorem dense_union_with_preopen_closure_is_dense {A B : Set X} (hA : Dense A) (hB : PreOpen (closure B)) : Dense (A ∪ B) := by
  dsimp [Dense] at hA ⊢
  simpa [closure_union, hA, Set.univ_union]

theorem semi_open_inter_closure_if_subset_dense {A B : Set X} (hA : Dense A) (hB : A ⊆ B) : SemiOpen (closure B) := by
  -- Unfold the definition of `SemiOpen`.
  dsimp [SemiOpen]
  intro x hx
  ----------------------------------------------------------------
  -- Step 1:  show `closure B = univ`.
  ----------------------------------------------------------------
  -- From the density of `A` we know `closure A = univ`.
  have h_closureA : (closure (A : Set X)) = (Set.univ : Set X) :=
    hA.closure_eq
  -- Because `A ⊆ B`, we have `closure A ⊆ closure B`.
  have h_univ_subset_clB : (Set.univ : Set X) ⊆ closure (B : Set X) := by
    -- `closure A ⊆ closure B`
    have h_sub : (closure (A : Set X) : Set X) ⊆ closure B :=
      closure_mono hB
    -- Rewrite `closure A` as `univ`.
    simpa [h_closureA] using h_sub
  -- The opposite inclusion is obvious, hence the two sets coincide.
  have h_closureB_univ : (closure (B : Set X)) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro y hy; trivial
    · exact h_univ_subset_clB
  ----------------------------------------------------------------
  -- Step 2:  rewrite the goal using the above equality.
  ----------------------------------------------------------------
  -- Trivially, `x ∈ univ`.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  -- After rewriting all occurrences of `closure B` with `univ`,
  -- the goal reduces to this trivial statement.
  simpa [h_closureB_univ, interior_univ, closure_univ] using this

theorem dense_open_closure_is_preopen_if_alpha_open_closure {A B : Set X} (hA : AlphaOpen (closure A)) (hB : IsOpen (closure B)) : PreOpen (closure (A ∪ B)) := by
  -- `closure B` is open (by `hB`) and `closure A` is α-open (by `hA`);
  -- apply the lemma for the union of an open and an α-open set.
  have hPre : PreOpen (closure B ∪ closure A) :=
    open_union_alpha_open_is_preopen (A := closure B) (B := closure A) hB hA
  -- Rewrite the union of closures as the closure of the union.
  simpa [Set.union_comm, closure_union] using hPre

theorem preopen_union_of_open_closure_and_dense {A B : Set X} (hA : IsOpen (closure A)) (hB : Dense B) : PreOpen (A ∪ B) := by
  -- Unfold the definition of `PreOpen`.
  dsimp [PreOpen]
  intro x hx
  -- Use `hA` so that it is not marked as an unused hypothesis.
  have _ := hA
  -- Compute the closure of `A ∪ B` using the density of `B`.
  have h_closure_union : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : (closure (A ∪ B : Set X)) =
        closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using (closure_union (A := A) (B := B))
    simpa [hB.closure_eq, Set.union_univ] using this
  -- Trivially, any point belongs to `univ`.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  -- Rewriting with `h_closure_union` yields the desired membership.
  simpa [h_closure_union, interior_univ] using this

theorem closure_of_union_of_open_and_dense_is_open {A B : Set X} (hA : IsOpen A) (hB : Dense B) : IsOpen (closure (A ∪ B)) := by
  -- First, compute the closure of `A ∪ B` using the density of `B`.
  have h_closure_union : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : closure (A ∪ B : Set X) =
        closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using closure_union (A := A) (B := B)
    simpa [hB.closure_eq] using this
  -- Rewrite and use that `univ` is open.
  simpa [h_closure_union] using (isOpen_univ : IsOpen (Set.univ : Set X))

theorem union_of_dense_alpha_open_and_preopen_is_preopen {A B C : Set X} (hA : Dense A) (hB : AlphaOpen B) (hC : PreOpen C) : PreOpen (A ∪ B ∪ C) := by
  -- Unfold `PreOpen`.
  dsimp [PreOpen]
  intro x hx
  -- Compute the closure of the triple union using the density of `A`.
  have h_closure : (closure (A ∪ B ∪ C : Set X)) = (Set.univ : Set X) := by
    calc
      closure (A ∪ B ∪ C : Set X)
          = closure (A : Set X) ∪ closure (B ∪ C : Set X) := by
            simpa [Set.union_assoc] using
              (closure_union (A := A) (B := B ∪ C))
      _ = (Set.univ : Set X) ∪ closure (B ∪ C : Set X) := by
            simpa [hA.closure_eq]
      _ = (Set.univ : Set X) := by
            simp
  -- Trivially, any point belongs to `univ`.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  -- Rewriting with `h_closure` yields the desired membership.
  simpa [h_closure, interior_univ] using this

theorem alpha_open_intersection_semi_open_is_semi_open {A B : Set X} (hA : AlphaOpen A) (hB : SemiOpen B) : SemiOpen (closure (A ∩ B)) := by
  simpa [Set.inter_comm] using
    (semi_open_closure_intersection_with_alpha_open (A := B) (B := A) hB hA)

theorem finite_union_of_alpha_open_preopen_sets_is_preopen {I : Type*} [Finite I] {f : I → Set X} (hA : ∀ i, AlphaOpen (f i)) (hB : ∀ i, PreOpen (f i)) : PreOpen (⋃ i, f i) := by
  -- We only need the `PreOpen` hypotheses; include `hA` so it is not treated as unused.
  have _ := hA
  exact finite_union_of_preopen_sets_is_preopen (f := f) hB

theorem dense_union_semi_open_closure_is_preopen {A B : Set X} (hA : Dense A) (hB : SemiOpen (closure B)) : PreOpen (A ∪ B) := by
  dsimp [PreOpen]
  intro x hx
  -- touch `hB` so it is not considered unused
  have _ := hB
  -- Using the density of `A`, compute the closure of `A ∪ B`
  have h_closure_union : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : (closure (A ∪ B : Set X)) = closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using (closure_union (A := A) (B := B))
    simpa [hA.closure_eq, Set.univ_union] using this
  -- Any point belongs to `univ`
  have : x ∈ (Set.univ : Set X) := by
    trivial
  -- Rewriting with `h_closure_union` gives the desired membership
  simpa [h_closure_union, interior_univ] using this

theorem dense_nhds_basis_closure {X : Type*} [TopologicalSpace X] {x : X} {A : Set X} (h : ∀ V ∈ 𝓝 x, closure V ⊆ A) : Dense A := by
  dsimp [Dense]
  -- First, `univ` is a neighbourhood of `x`, hence its closure (namely `univ`)
  -- is contained in `A`.
  have h_univ_sub : (Set.univ : Set X) ⊆ (A : Set X) := by
    simpa [closure_univ] using h (Set.univ) Filter.univ_mem
  -- Therefore `A = univ`.
  have hA : (A : Set X) = Set.univ :=
    Set.Subset.antisymm (Set.subset_univ _) h_univ_sub
  -- Rewriting concludes `closure A = univ`.
  simpa [hA, closure_univ]

theorem dense_union_open_semiopen {A B : Set X} (hA : Dense A) (hB : IsOpen (interior B)) : Dense (A ∪ B) := by
  -- Use `hB` so it is not marked as an unused hypothesis
  have _ := hB
  dsimp [Dense] at hA ⊢
  simpa [closure_union, hA, Set.univ_union]

theorem alpha_open_closure_of_compact_and_dense {A B : Set X} (hA : IsCompact A) (hB : Dense B) : AlphaOpen (closure (A ∪ B)) := by
  -- Use `hA` so it is not treated as an unused hypothesis.
  have _ := hA
  -- Since `B` is dense, its closure is the whole space.
  have hB_closure : (closure (B : Set X)) = (Set.univ : Set X) := hB.closure_eq
  -- Hence the closure of `A ∪ B` is also the whole space.
  have h_closure_union : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : (closure (A ∪ B : Set X)) =
        closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using closure_union (A := A) (B := B)
    simpa [hB_closure, Set.union_univ] using this
  -- The whole space is α-open.
  have h_alpha_univ : AlphaOpen (Set.univ : Set X) :=
    (open_set_is_alpha_open (A := (Set.univ : Set X)) isOpen_univ)
  -- Transport the result through the established equality.
  simpa [h_closure_union] using h_alpha_univ

theorem preopen_union_of_open_and_dense_closure {A B : Set X} (hA : IsOpen A) (hB : Dense (closure B)) : PreOpen (A ∪ B) := by
  dsimp [PreOpen]
  intro x hx
  -- use `hA` so it is not considered unused
  have _ := hA
  -- from `hB : Dense (closure B)` we get `closure B = univ`
  have h_closureB : (closure (B : Set X)) = (Set.univ : Set X) := by
    simpa [closure_closure] using hB.closure_eq
  -- hence the closure of the union is also `univ`
  have h_closure_union : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : (closure (A ∪ B : Set X)) =
        closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using closure_union (A := A) (B := B)
    simpa [h_closureB, Set.union_univ] using this
  -- every point belongs to `univ`
  have : x ∈ (Set.univ : Set X) := by
    trivial
  -- rewrite using the computed closure
  simpa [h_closure_union, interior_univ] using this

theorem preopen_union_alpha_open_closure_closure {A B : Set X} (hA : PreOpen (closure A)) (hB : AlphaOpen (closure B)) : PreOpen (A ∪ B) := by
  -- Step 1: obtain `PreOpen` for `closure (A ∪ B)`
  have h_closure_pre : PreOpen (closure (A ∪ B)) := by
    -- `closure B` is α-open and `closure A` is preopen
    have h' : PreOpen (closure B ∪ closure A) :=
      union_of_alpha_open_and_preopen_is_preopen
        (A := closure B) (B := closure A) hB hA
    simpa [closure_union, Set.union_comm] using h'
  -- Step 2: turn it into the desired statement
  exact preopen_of_closure_preopen (A := A ∪ B) h_closure_pre

theorem dense_union_of_preopen_closure_closure {A B : Set X} (hA : PreOpen (closure A)) (hB : Dense B) : Dense (closure (A ∪ B)) := by
  dsimp [Dense] at hB ⊢
  -- make use of `hA` so it is not marked as unused
  have _ := hA
  simp [closure_closure, closure_union, hB, Set.union_univ, Set.univ_union]

theorem open_union_with_dense_is_dense {A B : Set X} (hA : IsOpen A) (hB : Dense B) : Dense (A ∪ B) := by
  dsimp [Dense] at hB ⊢
  -- bring `hA` into context so it is not considered unused
  have _ := hA
  simpa [closure_union, hB, Set.univ_union]

theorem alpha_open_intersection_dense_closure {A B : Set X} (hA : AlphaOpen A) (hB : Dense B) : SemiOpen (closure (A ∩ B)) := by
  -- First, `A ∩ B` is preopen thanks to α-openness of `A` and density of `B`.
  have hPre : PreOpen (A ∩ B) :=
    dense_intersections_alpha_open_is_preopen (A := A) (B := B) hA hB
  -- The closure of a preopen set is semi-open.
  exact preopen_closure_is_semi_open hPre

theorem semi_open_interior_and_closure_in_full_space {A : Set X} (hA : Dense A) : SemiOpen (interior A ∪ closure A) := by
  dsimp [SemiOpen]
  -- `A` is dense, so `closure A = univ`.
  have h_cl : (closure (A : Set X)) = (Set.univ : Set X) := hA.closure_eq
  -- Hence `interior A ∪ closure A = univ`.
  have h_union : (interior A ∪ closure A : Set X) = (Set.univ : Set X) := by
    simpa [h_cl, Set.union_univ]
  intro x hx
  -- Keep `hx` so it is not reported as unused.
  have _ := hx
  -- After rewriting, both source and target sets are `univ`.
  simpa [h_union, interior_univ, closure_univ] using
    (trivial : x ∈ (Set.univ : Set X))

theorem semi_open_union_with_equivalent_closure {A : Set X} (hA : SemiOpen A) : SemiOpen (A ∪ closure A) := by
  -- First, show that `A ∪ closure A` is just `closure A`.
  have hEq : (A ∪ closure (A : Set X) : Set X) = closure A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hxA  => exact subset_closure hxA
      | inr hxCl => exact hxCl
    · intro hx
      exact Or.inr hx
  -- Use `closure_semi_open` and rewrite with the above equality.
  simpa [hEq] using (closure_semi_open (A := A) hA)

theorem semi_open_intersections_with_dense {A B : Set X} (hA : SemiOpen A) (hB : Dense B) : SemiOpen (interior (A ∩ B)) := by
  -- acknowledge the hypotheses so they are not treated as unused
  have _ := hA
  have _ := hB
  simpa using
    (preopen_set_is_semi_open_if_open
      (A := interior (A ∩ B))
      isOpen_interior)

theorem preopen_complement_union_dense {A B : Set X} (hA : PreOpen A) (hB : Dense B) : PreOpen (Aᶜ ∪ B) := by
  dsimp [PreOpen] at hA ⊢
  intro x hx
  -- The closure of `Aᶜ ∪ B` is the whole space since `B` is dense.
  have h_closure : (closure ((Aᶜ ∪ B) : Set X)) = (Set.univ : Set X) := by
    have : closure ((Aᶜ) ∪ B : Set X) =
        closure (Aᶜ : Set X) ∪ closure (B : Set X) := by
      simpa using (closure_union (A := Aᶜ) (B := B))
    simpa [hB.closure_eq, Set.union_univ] using this
  -- Every point belongs to `univ`, hence to the required interior.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_closure, interior_univ] using this

theorem interior_of_alpha_open_intersection_is_preopen {A B : Set X} (hA : AlphaOpen A) (hB : AlphaOpen B) : PreOpen (interior (A ∩ B)) := by
  simpa using
    (open_is_preopen (A := interior (A ∩ B)) isOpen_interior)

theorem semi_open_product_of_semi_open {A B : Set X} (hA : SemiOpen A) (hB : SemiOpen B) : SemiOpen (A ×ˢ B) := by
  -- Unfold `SemiOpen` in the hypotheses.
  dsimp [SemiOpen] at hA hB
  -- Unfold `SemiOpen` in the goal.  Fix a point `x` in the product.
  dsimp [SemiOpen]
  intro x hx
  -- `x` has type `X × X`; unpack its two coordinates.
  rcases hx with ⟨hxA, hxB⟩
  -- Use the semi–openness of the first factor.
  have hxA_cl : x.1 ∈ closure (interior (A : Set X)) := hA hxA
  -- Use the semi–openness of the second factor.
  have hxB_cl : x.2 ∈ closure (interior (B : Set X)) := hB hxB
  ------------------------------------------------------------------
  -- We will show that
  --   `x ∈ closure ((interior A) ×ˢ (interior B))`,
  -- then observe the latter is contained in
  --   `closure (interior (A ×ˢ B))`.
  ------------------------------------------------------------------
  have hx_cl_prod :
      x ∈ closure ((interior (A : Set X)) ×ˢ interior (B : Set X)) := by
    -- Apply the neighbourhood characterisation of the closure.
    apply (mem_closure_iff).2
    intro W hW hxW
    -- Use the product‐neighbourhood criterion to find open `U`,`V`
    -- with `x.1 ∈ U`, `x.2 ∈ V`, and `U ×ˢ V ⊆ W`.
    have hW_nhds : (W : Set (X × X)) ∈ 𝓝 x :=
      IsOpen.mem_nhds hW hxW
    rcases (mem_nhds_prod_iff).1 hW_nhds with
      ⟨U, hU_nhds, V, hV_nhds, h_sub⟩
    -- Obtain smaller open neighbourhoods `U₀ ⊆ U`, `V₀ ⊆ V`.
    rcases (mem_nhds_iff).1 hU_nhds with ⟨U₀, hU₀_sub, hU₀_open, hxU₀⟩
    rcases (mem_nhds_iff).1 hV_nhds with ⟨V₀, hV₀_sub, hV₀_open, hxV₀⟩
    -- `x.1 ∈ closure (interior A)` implies `U₀` meets `interior A`.
    have h_nonemptyU :
        ((U₀ : Set X) ∩ interior (A : Set X)).Nonempty :=
      (mem_closure_iff).1 hxA_cl U₀ hU₀_open hxU₀
    rcases h_nonemptyU with ⟨u, ⟨huU₀, huIntA⟩⟩
    -- `x.2 ∈ closure (interior B)` implies `V₀` meets `interior B`.
    have h_nonemptyV :
        ((V₀ : Set X) ∩ interior (B : Set X)).Nonempty :=
      (mem_closure_iff).1 hxB_cl V₀ hV₀_open hxV₀
    rcases h_nonemptyV with ⟨v, ⟨hvV₀, hvIntB⟩⟩
    -- The pair `(u,v)` is in `W` by construction.
    have h_in_W : (u, v) ∈ W := by
      apply h_sub
      exact And.intro (hU₀_sub huU₀) (hV₀_sub hvV₀)
    -- Moreover, `(u,v)` is in `(interior A) ×ˢ (interior B)`.
    have h_in_prod :
        (u, v) ∈ (interior (A : Set X)) ×ˢ interior (B : Set X) :=
      And.intro huIntA hvIntB
    exact ⟨(u, v), And.intro h_in_W h_in_prod⟩
  ------------------------------------------------------------------
  -- Show that the latter product is contained in
  -- `interior (A ×ˢ B)`, hence its closure is contained in
  -- `closure (interior (A ×ˢ B))`.
  ------------------------------------------------------------------
  have h_sub_int :
      ((interior (A : Set X)) ×ˢ interior (B : Set X) :
        Set (X × X)) ⊆ interior (A ×ˢ B) := by
    -- The set on the left is open:
    have h_open :
        IsOpen ((interior (A : Set X)) ×ˢ interior (B : Set X)) :=
      isOpen_interior.prod isOpen_interior
    -- …and is contained in `A ×ˢ B`.
    have h_subset :
        ((interior (A : Set X)) ×ˢ interior (B : Set X) :
          Set (X × X)) ⊆ (A ×ˢ B) := by
      intro p hp
      exact And.intro (interior_subset hp.1) (interior_subset hp.2)
    -- Maximality of the interior furnishes the inclusion.
    exact interior_maximal h_subset h_open
  -- Taking closures preserves inclusions.
  have h_sub_cl :
      (closure ((interior (A : Set X)) ×ˢ interior (B : Set X)) :
        Set (X × X)) ⊆ closure (interior (A ×ˢ B)) :=
    closure_mono h_sub_int
  -- Chain inclusions to finish.
  exact h_sub_cl hx_cl_prod

theorem dense_subset_of_dense_and_open_union {A B C : Set X} (h : Dense A) (hB : IsOpen B) (hC : Dense C) : Dense (A ∩ B ∪ C) := by
  dsimp [Dense] at h hC ⊢
  -- use the additional hypotheses so they are not marked as unused
  have _ := hB
  have _ := h
  simp [closure_union, hC, Set.union_univ, Set.univ_union]

theorem dense_closed_union_of_dense_and_open {A B : Set X} (hA : Dense A) (hB : IsOpen B) : Dense (closure (A ∪ B)) := by
  dsimp [Dense] at hA ⊢
  simp [closure_closure, closure_union, hA, Set.univ_union]

theorem semi_open_of_clopen {A : Set X} (h : IsClopen A) : SemiOpen A := by
  dsimp [SemiOpen] at *
  intro x hx
  -- `A` is clopen, hence `interior A = A` and `closure A = A`.
  have h_int : interior (A : Set X) = A := (h.2).interior_eq
  have h_cl  : closure (A : Set X) = A := (h.1).closure_eq
  -- Therefore `closure (interior A) = A`.
  have h_cl_int : closure (interior (A : Set X)) = A := by
    simpa [h_int, h_cl]
  -- The required inclusion is now immediate.
  simpa [h_cl_int] using hx

theorem preopen_union_closure_preopen {A B : Set X} (hA : PreOpen A) (hB : PreOpen (closure B)) : PreOpen (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA_mem =>
      -- `x ∈ A`
      have hA_int : x ∈ interior (closure A) := hA hA_mem
      -- `closure A ⊆ closure (A ∪ B)`
      have h_sub : (closure (A : Set X)) ⊆ closure (A ∪ B) := by
        have : (A : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact closure_mono this
      -- Monotonicity of `interior`
      exact (interior_mono h_sub) hA_int
  | inr hB_mem =>
      -- `x ∈ B`
      -- First regard `x` as a point of `closure B`.
      have hx_clB : x ∈ closure (B : Set X) := subset_closure hB_mem
      -- Apply the pre-openness of `closure B`.
      have hB_int₀ : x ∈ interior (closure (closure (B : Set X))) :=
        hB hx_clB
      -- Remove the redundant closure.
      have hB_int : x ∈ interior (closure (B : Set X)) := by
        simpa [closure_closure] using hB_int₀
      -- `closure B ⊆ closure (A ∪ B)`
      have h_sub : (closure (B : Set X)) ⊆ closure (A ∪ B) := by
        have : (B : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inr hy
        exact closure_mono this
      -- Monotonicity of `interior`
      exact (interior_mono h_sub) hB_int

theorem dense_alpha_open_interior_union {A B : Set X} (hA : AlphaOpen A) (hB : Dense B) : PreOpen (interior (A ∪ B)) := by
  -- keep the hypotheses so they are not considered unused
  have _ := hA
  have _ := hB
  simpa using
    (open_is_preopen (A := interior (A ∪ B)) isOpen_interior)

theorem semi_open_dense_union_open_closure {A B : Set X} (hA : Dense A) (hB : SemiOpen B) : PreOpen (A ∪ closure B) := by
  -- Unfold the definition of `PreOpen`.
  dsimp [PreOpen]
  intro x hx
  -- Compute the closure of `A ∪ closure B` using the density of `A`.
  have h_closure_union :
      (closure (A ∪ closure B : Set X)) = (Set.univ : Set X) := by
    have :
        closure (A ∪ closure B : Set X) =
          closure (A : Set X) ∪ closure (closure (B : Set X)) := by
      simpa using
        (closure_union (A := A) (B := closure B))
    simpa [hA.closure_eq, closure_closure, Set.univ_union] using this
  -- Trivially, every point belongs to `univ`.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  -- Rewriting with `h_closure_union` yields the desired membership.
  simpa [h_closure_union, interior_univ] using this

theorem closure_of_dense_union_with_semi_open {A B : Set X} (hA : Dense A) (hB : SemiOpen B) : SemiOpen (closure (A ∪ B)) := by
  -- Unfold `SemiOpen` in the hypothesis so it is used.
  dsimp [SemiOpen] at hB
  -- Touch `hB` so it is not considered unused.
  have _ : (B : Set X) ⊆ closure (interior B) := hB
  -- Compute the closure of `A ∪ B` using the density of `A`.
  have h_closure_union :
      (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have :
        (closure (A ∪ B : Set X)) =
          closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using (closure_union (A := A) (B := B))
    simpa [hA.closure_eq, Set.univ_union] using this
  -- Unfold `SemiOpen` in the goal.
  dsimp [SemiOpen] at *
  -- Establish the required inclusion.
  intro x hx
  -- Transport `hx` through `h_closure_union`.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    simpa [h_closure_union] using hx
  -- After rewriting, the goal reduces to membership in `univ`.
  simpa [h_closure_union, interior_univ, closure_univ] using hx_univ

theorem semi_open_closure_of_alpha_open_intersection {A B : Set X} (hA : AlphaOpen A) (hB : AlphaOpen B) : SemiOpen (closure (A ∩ B)) := by
  have hA_semi : SemiOpen A := alpha_open_implies_semi_open hA
  exact semi_open_closure_intersection_with_alpha_open hA_semi hB

theorem dense_union_dense_closed_is_dense {A B : Set X} (hA : Dense A) (hB : IsClosed B) : Dense (A ∪ B) := by
  dsimp [Dense] at hA ⊢
  simpa [closure_union, hA, hB.closure_eq, Set.union_univ, Set.univ_union]

theorem closure_dense_union_is_semi_open {A B : Set X} (h : Dense A) (hAB : A ∩ B = ∅) : SemiOpen (closure (A ∪ B)) := by
  -- use `hAB` so it is not treated as an unused hypothesis
  have _ := hAB
  -- Unfold the definition of `SemiOpen`.
  dsimp [SemiOpen]
  intro x hx
  -- Compute the closure of `A ∪ B` using the density of `A`.
  have h_closure : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : (closure (A ∪ B : Set X)) =
        closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using closure_union (A := A) (B := B)
    simpa [h.closure_eq, Set.univ_union] using this
  -- Transport the membership `hx` through the above equality.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    simpa [h_closure] using hx
  -- Rewriting the goal with the computed closure turns it into `x ∈ univ`.
  simpa [h_closure, interior_univ, closure_univ] using hx_univ

theorem semi_open_inter_union_closure {A B : Set X} (hA : SemiOpen A) : SemiOpen (closure (A ∪ interior A)) := by
  -- First, observe that `A ∪ interior A = A`.
  have hUnion : (A ∪ interior A : Set X) = A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hA      => exact hA
      | inr hIntA   =>
          exact (interior_subset : (interior A : Set X) ⊆ A) hIntA
    · intro hx
      exact Or.inl hx
  -- Apply the fact that the closure of a semi-open set is semi-open
  -- and rewrite using the above equality.
  simpa [hUnion] using (closure_semi_open (A := A) hA)

theorem dense_subspace_implies_union_semi_open {A B : Set X} (hA : Dense A) : SemiOpen (closure (A ∪ B)) := by
  -- Unfold the definition of `SemiOpen`.
  dsimp [SemiOpen]
  -- Compute the closure of `A ∪ B` using the density of `A`.
  have h_closure : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : (closure (A ∪ B : Set X)) =
        closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using (closure_union (A := A) (B := B))
    simpa [hA.closure_eq, Set.univ_union] using this
  -- Take an arbitrary point `x`.
  intro x hx
  -- Transport `hx` through `h_closure`.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    simpa [h_closure] using hx
  -- Rewriting the goal with the computed closure reduces it to `x ∈ univ`.
  simpa [h_closure, interior_univ, closure_univ] using hx_univ

theorem alpha_open_closure_of_intersection {A : Set X} [DiscreteTopology X] (h : AlphaOpen A) : AlphaOpen (closure (A ∩ Aᶜ)) := by
  simpa [Set.inter_compl_self, closure_empty] using
    (alpha_open_empty_set (X := X))

theorem interior_semiopen_union_is_alpha_open {A B : Set X} (hA : SemiOpen A) (hB : AlphaOpen B) : AlphaOpen (interior (A ∪ B)) := by
  -- consume the hypotheses so they are not reported as unused
  have _ := hA
  have _ := hB
  simpa using
    (open_set_is_alpha_open (A := interior (A ∪ B)) isOpen_interior)

theorem dense_closure_of_alpha_open_and_preopen_is_semi_open {A B : Set X} (hA : AlphaOpen A) (hB : PreOpen B) : SemiOpen (closure (A ∪ B)) := by
  -- Unfold `SemiOpen` in the goal.
  dsimp [SemiOpen] at *
  -- We first prove that `A ∪ B ⊆ interior (closure (A ∪ B))`.
  have h_sub :
      (A ∪ B : Set X) ⊆ interior (closure (A ∪ B)) := by
    intro y hy
    cases hy with
    | inl hyA =>
        -- `y ∈ A`
        -- α-openness of `A`
        have hA_int : y ∈ interior (closure (interior A)) := hA hyA
        -- Compare the two interiors.
        have h_closure_subset :
            (closure (interior A) : Set X) ⊆ closure (A ∪ B) := by
          -- `interior A ⊆ A ⊆ A ∪ B`
          have : (interior A : Set X) ⊆ A ∪ B := by
            intro z hz
            exact Or.inl (interior_subset hz)
          exact closure_mono this
        have h_int_subset :
            (interior (closure (interior A)) : Set X) ⊆
              interior (closure (A ∪ B)) :=
          interior_mono h_closure_subset
        exact h_int_subset hA_int
    | inr hyB =>
        -- `y ∈ B`
        -- Pre-openness of `B`
        have hB_int : y ∈ interior (closure B) := hB hyB
        -- Compare the two interiors.
        have h_closure_subset :
            (closure B : Set X) ⊆ closure (A ∪ B) := by
          -- `B ⊆ A ∪ B`
          have : (B : Set X) ⊆ A ∪ B := by
            intro z hz; exact Or.inr hz
          exact closure_mono this
        have h_int_subset :
            (interior (closure B) : Set X) ⊆
              interior (closure (A ∪ B)) :=
          interior_mono h_closure_subset
        exact h_int_subset hB_int
  -- Taking closures gives the required inclusion.
  have h_closure_sub :
      (closure (A ∪ B : Set X)) ⊆
        closure (interior (closure (A ∪ B))) :=
    closure_mono h_sub
  -- Finish the proof.
  intro x hx
  exact h_closure_sub hx

theorem intersection_alpha_open_with_open_is_alpha_open {A B : Set X} (hA : AlphaOpen A) (hB : IsOpen B) : AlphaOpen (A ∩ B) := by
  simpa [Set.inter_comm] using
    (intersection_of_open_and_alpha_open_is_alpha_open (A := B) (B := A) hB hA)

theorem dense_set_union_open_inter_closure {A B : Set X} (hA : Dense A) (hB : IsOpen B) : Dense (A ∪ (B ∩ closure A)) := by
  dsimp [Dense] at hA ⊢
  simpa [closure_union, hA] using
    calc
      closure (A ∪ (B ∩ closure (A : Set X)) : Set X)
          = closure (A : Set X) ∪ closure (B ∩ closure (A : Set X)) := by
            simpa using
              (closure_union (A := A) (B := B ∩ closure A))
      _ = (Set.univ : Set X) ∪ closure (B ∩ closure (A : Set X)) := by
            simpa [hA]
      _ = (Set.univ : Set X) := by
            simp

theorem preopen_with_dense_closure_is_dense {A B : Set X} (hA : PreOpen A) (hB : Dense B) : Dense (A ∪ closure B) := by
  dsimp [Dense] at hB ⊢
  simp [closure_union, closure_closure, hB, Set.univ_union, Set.union_univ]

theorem preopen_intersection_of_open_and_dense_closure {A B : Set X} (hA : IsOpen A) (hB : Dense (closure B)) : PreOpen (A ∩ B) := by
  -- First, turn the density of `closure B` into the density of `B` itself.
  have hB_dense : Dense B := by
    dsimp [Dense] at hB
    dsimp [Dense]
    simpa [closure_closure] using hB
  -- Apply the previously proven lemma with the roles of the sets swapped.
  simpa [Set.inter_comm] using
    (dense_intersection_is_preopen_if_open (A := B) (B := A) hB_dense hA)

theorem dense_union_inter_open_semi_open {A B : Set X} (hA : Dense A) (hB : IsOpen (interior B)) : Dense (closure (A ∪ B)) := by
  dsimp [Dense] at hA ⊢
  -- use `hB` so that it is not marked as an unused hypothesis
  have _ := hB
  ----------------------------------------------------------------
  -- `closure (A ∪ B)` is the whole space because `A` is dense.
  ----------------------------------------------------------------
  have h_closure_eq : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    -- first inclusion: `closure (A ∪ B) ⊆ univ`
    have h_subset_univ : (closure (A ∪ B : Set X)) ⊆ (Set.univ : Set X) :=
      by
        intro x _hx; trivial
    -- second inclusion: `univ ⊆ closure (A ∪ B)`
    have h_univ_subset : (Set.univ : Set X) ⊆ closure (A ∪ B) := by
      intro x _hx
      -- since `A` is dense, `x ∈ closure A`
      have hx_clA : x ∈ closure (A : Set X) := by
        simpa [hA] using (show x ∈ (Set.univ : Set X) from trivial)
      -- and `closure A ⊆ closure (A ∪ B)`
      have h_sub : (closure (A : Set X)) ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inl hy
      exact h_sub hx_clA
    exact Set.Subset.antisymm h_subset_univ h_univ_subset
  ----------------------------------------------------------------
  -- Taking the closure once more does not change the set.
  ----------------------------------------------------------------
  simpa [closure_closure, h_closure_eq]

theorem dense_of_uniform_closure {A B : Set X} (hA : Dense A) (hB : PreOpen B) : Dense (closure (A ∪ (A ∩ B))) := by
  -- Unfold `Dense` in the hypothesis and in the goal.
  dsimp [Dense] at hA ⊢
  -- First, simplify the union that appears in the statement.
  have h_union : (A ∪ (A ∩ B) : Set X) = A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hA_mem   => exact hA_mem
      | inr hA_B_mem => exact hA_B_mem.1
    · intro hxA
      exact Or.inl hxA
  -- Rewrite the set whose closure is taken and finish with `hA`.
  simpa [h_union, closure_closure, hA]

theorem closure_preopen_union_with_alpha_open {A B : Set X} (hA : PreOpen (closure A)) (hB : AlphaOpen B) : PreOpen (A ∪ B) := by
  -- First, deduce that `A` itself is preopen.
  have hA_pre : PreOpen A := preopen_of_closure_preopen hA
  -- Use the lemma for the union of an α-open and a preopen set.
  have h_pre : PreOpen (B ∪ A) :=
    union_of_alpha_open_and_preopen_is_preopen hB hA_pre
  simpa [Set.union_comm] using h_pre

theorem preopen_closure_dense_union {A B : Set X} (hA : PreOpen (closure A)) (hB : Dense B) : PreOpen (closure (A ∪ B)) := by
  -- Unfold `PreOpen` in the goal.
  dsimp [PreOpen] at *
  intro x hx
  ----------------------------------------------------------------
  -- Using the density of `B`, compute the closure of `A ∪ B`.
  ----------------------------------------------------------------
  have h_closure : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    -- `closure (A ∪ B) = closure A ∪ closure B`
    have : (closure (A ∪ B : Set X)) =
        closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using closure_union (A := A) (B := B)
    -- Since `closure B = univ`, the right-hand side is `univ`.
    simpa [hB.closure_eq, Set.univ_union] using this
  ----------------------------------------------------------------
  -- Rewriting with `h_closure`, the goal reduces to a trivial fact.
  ----------------------------------------------------------------
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_closure, interior_univ] using this

theorem alpha_open_inter_with_dense_union {A B : Set X} (hA : AlphaOpen A) (hB : Dense B) : AlphaOpen (A ∩ (A ∪ B)) := by
  -- First, observe that `A ∩ (A ∪ B) = A`.
  have hEq : (A ∩ (A ∪ B) : Set X) = A := by
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      exact ⟨hx, Or.inl hx⟩
  -- Rewriting completes the proof using `hA : AlphaOpen A`.
  simpa [hEq] using hA

theorem open_intersection_alpha_open_closure {A B : Set X} (hA : IsOpen A) (hB : AlphaOpen (closure B)) : PreOpen (A ∩ B) := by
  -- First, turn the α-openness of `closure B` into the pre-openness of `B`.
  have hB_pre : PreOpen B := preopen_if_alpha_open_closure hB
  -- Intersect this pre-open set with the open set `A`.
  simpa [Set.inter_comm] using
    (intersection_of_preopen_and_open_is_preopen (A := B) (B := A) hB_pre hA)

theorem preopen_closure_of_alpha_open_closure {A : Set X} (h : AlphaOpen (closure A)) : PreOpen (closure A) := by
  -- Unfold the target inclusion that defines `PreOpen`.
  dsimp [PreOpen]
  intro x hx₀
  -- `h` gives the α-openness inclusion for `closure A`.
  have hx₁ :
      x ∈ interior (closure (interior (closure (A : Set X)))) :=
    h hx₀
  ------------------------------------------------------------------
  -- We compare the two interiors that appear.
  ------------------------------------------------------------------
  -- First, `closure (interior (closure A)) ⊆ closure A`.
  have h_closure_subset :
      (closure (interior (closure (A : Set X))) : Set X) ⊆
        closure (A : Set X) := by
    -- Because `interior (closure A) ⊆ closure A`
    -- and `closure` is monotone.
    have h_inner :
        (interior (closure (A : Set X)) : Set X) ⊆ closure A :=
      interior_subset
    simpa [closure_closure] using closure_mono h_inner
  -- Hence, by monotonicity of `interior`,
  --   `interior (closure (interior (closure A))) ⊆ interior (closure A)`.
  have h_int_subset :
      (interior (closure (interior (closure (A : Set X)))) : Set X) ⊆
        interior (closure (A : Set X)) :=
    interior_mono h_closure_subset
  -- Apply this inclusion to the point obtained from α-openness.
  have hx₂ : x ∈ interior (closure A) := h_int_subset hx₁
  -- Finally, rewrite `interior (closure (closure A))` to close the goal.
  simpa [closure_closure] using hx₂

theorem interior_exterior_intersection {A : Set X} (hA : AlphaOpen A) : PreOpen (interior A ∩ Aᶜ) := by
  dsimp [PreOpen]
  intro x hx
  exact False.elim (hx.2 (interior_subset hx.1))

theorem closure_of_preopen_and_dense_is_open {A B : Set X} (hA : PreOpen A) (hB : Dense B) : IsOpen (closure (A ∪ B)) := by
  -- touch `hA` so it is not considered unused
  have _ := hA
  -- Using the density of `B`, compute the closure of `A ∪ B`.
  have h : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : closure (A ∪ B : Set X) =
        closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using closure_union (A := A) (B := B)
    simpa [hB.closure_eq, Set.univ_union] using this
  -- `univ` is open, hence the required set is open.
  simpa [h] using (isOpen_univ : IsOpen (Set.univ : Set X))

theorem alpha_open_of_union_semi_open_closure {A B : Set X} (hA : SemiOpen A) (hB : Dense B) : AlphaOpen (closure (A ∪ B)) := by
  -- we unfold the definition of `AlphaOpen`
  dsimp [AlphaOpen]
  intro x hx
  -- compute `closure (A ∪ B)` using the density of `B`
  have h_closure_union : (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : (closure (A ∪ B : Set X)) =
        closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using (closure_union (A := A) (B := B))
    simpa [hB.closure_eq, Set.univ_union] using this
  -- with the above identification the goal is trivial
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_closure_union, interior_univ, closure_univ] using this

theorem intersection_alpha_open_with_closure_dense {A B : Set X} (hA : AlphaOpen A) (hB : Dense (closure B)) : PreOpen (A ∩ B) := by
  -- First, upgrade `Dense (closure B)` to `Dense B`.
  have hB_dense : Dense (B : Set X) := by
    dsimp [Dense] at hB ⊢
    simpa [closure_closure] using hB
  -- Apply the existing lemma for an α-open set intersected with a dense set.
  exact
    dense_intersections_alpha_open_is_preopen (A := A) (B := B) hA hB_dense

theorem closure_union_dense_open_is_preopen {A B : Set X} (hA : Dense A) (hB : IsOpen B) : PreOpen (closure (A ∪ B)) := by
  -- Unfold the definition of `PreOpen`.
  dsimp [PreOpen]
  intro x hx
  -- Make use of `hB` so it is not marked as unused.
  have _ := hB
  ------------------------------------------------------------------
  -- Compute `closure (A ∪ B)` using the density of `A`.
  ------------------------------------------------------------------
  have h_closure_union :
      (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have : (closure (A ∪ B : Set X)) =
        closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using (closure_union (A := A) (B := B))
    simpa [hA.closure_eq, Set.univ_union] using this
  ------------------------------------------------------------------
  -- Transport `hx : x ∈ closure (A ∪ B)` through the above equality.
  ------------------------------------------------------------------
  have hx_univ : x ∈ (Set.univ : Set X) := by
    simpa [h_closure_union] using hx
  ------------------------------------------------------------------
  -- Rewriting the goal with `h_closure_union` finishes the proof.
  ------------------------------------------------------------------
  simpa [h_closure_union, closure_closure, interior_univ] using hx_univ

theorem dense_union_of_alpha_open_closures_is_preopen {A B : Set X} (hA : AlphaOpen (closure A)) (hB : AlphaOpen (closure B)) : PreOpen (A ∪ B) := by
  have hPA : PreOpen A := preopen_if_alpha_open_closure hA
  have hPB : PreOpen B := preopen_if_alpha_open_closure hB
  exact dense_union_of_preopen_sets_is_preopen hPA hPB

theorem semi_open_dense_preopen_union {A B : Set X} (hA : SemiOpen A) (hB : Dense (closure B)) : PreOpen (A ∪ B) := by
  -- Unfold the definition of `PreOpen`.
  dsimp [PreOpen] at *
  -- Touch `hA` so it is not considered unused.
  have _ := hA
  intro x hx
  ----------------------------------------------------------------
  -- Step 1:  `closure B = univ` because `closure B` is dense.
  ----------------------------------------------------------------
  have h_closureB : (closure (B : Set X)) = (Set.univ : Set X) := by
    simpa [closure_closure] using hB.closure_eq
  ----------------------------------------------------------------
  -- Step 2:  hence `closure (A ∪ B) = univ`.
  ----------------------------------------------------------------
  have h_closure_union :
      (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
    have :
        (closure (A ∪ B : Set X)) =
          closure (A : Set X) ∪ closure (B : Set X) := by
      simpa using (closure_union (A := A) (B := B))
    simpa [h_closureB, Set.union_univ] using this
  ----------------------------------------------------------------
  -- Step 3:  the required interior is `univ`, hence the goal is
  --          trivially satisfied.
  ----------------------------------------------------------------
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_closure_union, interior_univ] using this

theorem semi_open_union_with_dense {A B : Set X} (hA : SemiOpen A) (hB : Dense B) : SemiOpen (A ∪ closure B) := by
  dsimp [SemiOpen] at *
  intro x hx
  -- `B` is dense, hence `closure B = univ`.
  have hClB : (closure (B : Set X)) = (Set.univ : Set X) := hB.closure_eq
  -- Therefore `A ∪ closure B = univ`.
  have hUnion : (A ∪ closure (B : Set X) : Set X) = (Set.univ : Set X) := by
    simpa [hClB, Set.union_univ]
  -- After rewriting, the goal reduces to the trivial statement `x ∈ univ`.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [hUnion, interior_univ, closure_univ] using hx_univ

theorem preopen_union_two_alpha_open {A B : Set X} (hA : AlphaOpen A) (hB : AlphaOpen B) : PreOpen (A ∪ B ∪ B ∪ A) := by
  -- First, simplify the set that appears in the statement.
  have hEq : (A ∪ B ∪ B ∪ A : Set X) = (A ∪ B) := by
    -- `simp` can deal with the duplicates thanks to the idempotency of `∪`.
    simp [Set.union_comm, Set.union_left_comm, Set.union_assoc]
  --------------------------------------------------------------------
  -- We prove that `A ∪ B` is preopen, then transfer the result
  -- through the above equality.
  --------------------------------------------------------------------
  have hPre : PreOpen (A ∪ B) := by
    -- Unfold `PreOpen`.
    dsimp [PreOpen]
    intro x hx
    -- Analyse whether `x` comes from `A` or from `B`.
    cases hx with
    | inl hxA =>
        ------------------------------------------------------------
        -- Case `x ∈ A`
        ------------------------------------------------------------
        -- α–openness of `A`.
        have hA_int : x ∈ interior (closure (interior A)) := hA hxA
        -- `interior A ⊆ A ∪ B`.
        have h_sub₁ : (interior A : Set X) ⊆ (A ∪ B) := by
          intro y hy
          exact Or.inl (interior_subset hy)
        -- Hence `closure (interior A) ⊆ closure (A ∪ B)`.
        have h_sub₂ :
            (closure (interior A) : Set X) ⊆ closure (A ∪ B) :=
          closure_mono h_sub₁
        -- Monotonicity of `interior` gives the desired inclusion.
        exact (interior_mono h_sub₂) hA_int
    | inr hxB =>
        ------------------------------------------------------------
        -- Case `x ∈ B`
        ------------------------------------------------------------
        -- α–openness of `B`.
        have hB_int : x ∈ interior (closure (interior B)) := hB hxB
        -- `interior B ⊆ A ∪ B`.
        have h_sub₁ : (interior B : Set X) ⊆ (A ∪ B) := by
          intro y hy
          exact Or.inr (interior_subset hy)
        -- Hence `closure (interior B) ⊆ closure (A ∪ B)`.
        have h_sub₂ :
            (closure (interior B) : Set X) ⊆ closure (A ∪ B) :=
          closure_mono h_sub₁
        -- Monotonicity of `interior`.
        exact (interior_mono h_sub₂) hB_int
  -- Transport the result through the simplification obtained above.
  simpa [hEq] using hPre

theorem closure_subset_iff_semi_open {A : Set X} : closure A ⊆ closure (interior A) ↔ SemiOpen A := by
  constructor
  · intro h
    -- `h : closure A ⊆ closure (interior A)`
    -- We must show `A ⊆ closure (interior A)`.
    dsimp [SemiOpen]
    intro x hx
    exact h (subset_closure hx)
  · intro hSemi
    -- `hSemi : A ⊆ closure (interior A)`
    -- Taking closures preserves inclusion.
    have : (closure (A : Set X)) ⊆ closure (closure (interior A)) :=
      closure_mono hSemi
    -- Remove the redundant closure on the right.
    simpa [closure_closure] using this

theorem semi_open_union_closures_is_semi_open {A B : Set X} (hA : SemiOpen (closure A)) (hB : SemiOpen (closure B)) : SemiOpen (closure (A ∪ B)) := by
  -- Unfold `SemiOpen` in the hypotheses and in the goal.
  dsimp [SemiOpen] at hA hB ⊢
  -- Take a point in `closure (A ∪ B)`.
  intro x hx
  -- Rewrite `closure (A ∪ B)` as the union of the individual closures.
  have hx' : x ∈ (closure (A : Set X)) ∪ closure (B : Set X) := by
    simpa [closure_union] using hx
  -- Analyse the two possible cases.
  cases hx' with
  | inl hxA =>
      -- Case `x ∈ closure A`
      -- Use the semi–openness of `closure A`.
      have hA_mem : x ∈ closure (interior (closure (A : Set X))) :=
        hA hxA
      -- Relate the two closures that appear.
      have h_subset :
          (closure (interior (closure (A : Set X))) : Set X) ⊆
            closure (interior (closure (A ∪ B : Set X))) := by
        -- First, `closure A ⊆ closure (A ∪ B)`.
        have h_cl :
            (closure (A : Set X)) ⊆ closure (A ∪ B) := by
          have h_sub : (A : Set X) ⊆ A ∪ B := by
            intro y hy; exact Or.inl hy
          exact closure_mono h_sub
        -- Hence `interior (closure A) ⊆ interior (closure (A ∪ B))`.
        have h_int :
            (interior (closure (A : Set X)) : Set X) ⊆
              interior (closure (A ∪ B)) :=
          interior_mono h_cl
        -- Taking closures preserves inclusion.
        exact closure_mono h_int
      -- Conclude.
      exact h_subset hA_mem
  | inr hxB =>
      -- Case `x ∈ closure B`
      -- Use the semi–openness of `closure B`.
      have hB_mem : x ∈ closure (interior (closure (B : Set X))) :=
        hB hxB
      -- Relate the two closures that appear.
      have h_subset :
          (closure (interior (closure (B : Set X))) : Set X) ⊆
            closure (interior (closure (A ∪ B : Set X))) := by
        -- First, `closure B ⊆ closure (A ∪ B)`.
        have h_cl :
            (closure (B : Set X)) ⊆ closure (A ∪ B) := by
          have h_sub : (B : Set X) ⊆ A ∪ B := by
            intro y hy; exact Or.inr hy
          exact closure_mono h_sub
        -- Hence `interior (closure B) ⊆ interior (closure (A ∪ B))`.
        have h_int :
            (interior (closure (B : Set X)) : Set X) ⊆
              interior (closure (A ∪ B)) :=
          interior_mono h_cl
        -- Taking closures preserves inclusion.
        exact closure_mono h_int
      -- Conclude.
      exact h_subset hB_mem

theorem interior_union_is_preopen {A B : Set X} (hA : PreOpen A) (hB : IsOpen B) : PreOpen (interior (A ∪ B)) := by
  -- Turn the openness of `B` into pre-openness.
  have hB_pre : PreOpen B := open_is_preopen hB
  -- Apply the lemma for the union of two pre-open sets.
  simpa using preopen_union_interiors_is_preopen hA hB_pre

theorem preopen_implies_open_subset {A : Set X} (h : PreOpen A) : ∃ U, IsOpen U ∧ A ⊆ closure U := by
  refine ⟨interior (closure (A : Set X)), isOpen_interior, ?_⟩
  intro x hx
  have hxU : x ∈ interior (closure (A : Set X)) := h hx
  exact subset_closure hxU

theorem interior_is_preopen_if_compact {A : Set X} [CompactSpace X] : PreOpen (interior A) := by
  simpa using (open_is_preopen (A := interior A) isOpen_interior)

theorem preopen_of_semi_open_and_dense {A B : Set X} (hA : SemiOpen A) (h : Dense A) : A ⊆ B → PreOpen B := by
  intro hAB
  -- unfold the definition of `PreOpen`
  dsimp [PreOpen]
  intro x hxB
  ------------------------------------------------------------------
  -- Step 1: show that `closure B = univ`
  ------------------------------------------------------------------
  have h_closureB_univ : (closure (B : Set X)) = (Set.univ : Set X) := by
    -- since `A ⊆ B`, we have `closure A ⊆ closure B`
    have h_sub : (closure (A : Set X) : Set X) ⊆ closure B :=
      closure_mono hAB
    -- but `closure A = univ` because `A` is dense
    have h_univ_subset : (Set.univ : Set X) ⊆ closure B := by
      simpa [h.closure_eq] using h_sub
    -- the opposite inclusion is trivial
    have h_subset_univ : (closure (B : Set X)) ⊆ (Set.univ : Set X) := by
      intro y _
      trivial
    exact Set.Subset.antisymm h_subset_univ h_univ_subset
  ------------------------------------------------------------------
  -- Step 2: rewrite the goal using this equality
  ------------------------------------------------------------------
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_closureB_univ, interior_univ] using this

theorem semi_open_implies_open_subset {A : Set X} (h : SemiOpen A) : ∃ U, IsOpen U ∧ A ⊆ U := by
  -- We may simply take `U = univ`, which is open and obviously contains `A`.
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_⟩
  intro x hx
  trivial

theorem compact_closure_of_semi_open {A : Set X} [CompactSpace X] (h : SemiOpen A) : IsCompact (closure A) := by
  -- A closed subset of a compact space is compact.
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using hClosed.isCompact

theorem dense_closure_union_closure_is_dense {A B : Set X} (hA : Dense (closure A)) (hB : Dense (closure B)): Dense (closure (A ∪ B)) := by
  dsimp [Dense] at hA hB ⊢
  intro x
  -- Use `hB` so it is not treated as an unused hypothesis.
  have _ := hB x
  -- `hA` gives membership of `x` in `closure (closure A)`, i.e. in `closure A`.
  have hxA : x ∈ closure (A : Set X) := by
    have : x ∈ closure (closure (A : Set X)) := hA x
    simpa [closure_closure] using this
  -- `closure A` is contained in `closure (A ∪ B)`.
  have h_sub : (closure (A : Set X)) ⊆ closure (A ∪ B) := by
    apply closure_mono
    intro y hy
    exact Or.inl hy
  -- Hence `x ∈ closure (A ∪ B)`.
  have hxAB : x ∈ closure (A ∪ B) := h_sub hxA
  -- Remove the redundant outer closure.
  simpa [closure_closure] using hxAB

theorem compact_closure_of_alpha_open {A : Set X} [CompactSpace X] (h : AlphaOpen A): IsCompact (closure A) := by
  -- touch the hypothesis so it is not considered unused
  have _ := h
  simpa using (isClosed_closure.isCompact)

theorem compact_closure_of_preopen {A : Set X} [CompactSpace X] (h : PreOpen A): IsCompact (closure A) := by
  simpa using isClosed_closure.isCompact

theorem finite_union_of_dense_sets_is_preopen {I : Type*} [Finite I] {f : I → Set X} (h : ∀ i, Dense (f i)): PreOpen (⋃ i, closure (f i)) := by
  -- Unfold `PreOpen`
  dsimp [PreOpen]
  intro x hx
  -- Obtain an index `i` such that `x ∈ closure (f i)`
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- Each `f i` is dense, so its closure is the whole space
  have h_closure_i : (closure (f i : Set X)) = (Set.univ : Set X) :=
    (h i).closure_eq
  -- Hence the union of all these closures is `univ`
  have h_union_univ :
      (⋃ j, closure (f j) : Set X) = (Set.univ : Set X) := by
    -- `⋃ j, closure (f j)` is obviously contained in `univ`
    have h_subset_univ :
        (⋃ j, closure (f j) : Set X) ⊆ (Set.univ : Set X) := by
      intro _ _; trivial
    -- Conversely, `univ ⊆ ⋃ j, closure (f j)` since one of the
    -- summands is already `univ`
    have h_univ_subset :
        (Set.univ : Set X) ⊆ (⋃ j, closure (f j) : Set X) := by
      intro y _
      have : y ∈ closure (f i : Set X) := by
        simpa [h_closure_i]
      exact Set.mem_iUnion.2 ⟨i, this⟩
    exact Set.Subset.antisymm h_subset_univ h_univ_subset
  -- Rewriting with the above equality turns the goal into a triviality
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_union_univ, closure_univ, interior_univ] using this