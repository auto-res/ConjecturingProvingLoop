

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P1 A) (hB : P1 B) (hC : P1 C) : P1 (A ×ˢ B ×ˢ C) := by
  -- First, obtain `P1` for the product `B ×ˢ C` (a subset of `Y × Z`).
  have hBC : P1 (B ×ˢ C) :=
    P1_prod (X := Y) (Y := Z) (A := B) (B := C) hB hC
  -- Combine `hA` with `hBC` to get the desired result.
  simpa using
    (P1_prod (X := X) (Y := Y × Z) (A := A) (B := (B ×ˢ C)) hA hBC)

theorem P2_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P2 A) (hB : P2 B) (hC : P2 C) : P2 (A ×ˢ B ×ˢ C) := by
  -- First, obtain `P2` for the product `B ×ˢ C`.
  have hBC : P2 (B ×ˢ C) :=
    P2_prod (X := Y) (Y := Z) (A := B) (B := C) hB hC
  -- Combine `hA` with `hBC` to get the desired result.
  simpa using
    (P2_prod (X := X) (Y := Y × Z) (A := A) (B := (B ×ˢ C)) hA hBC)

theorem P3_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P3 A) (hB : P3 B) (hC : P3 C) : P3 (A ×ˢ B ×ˢ C) := by
  -- First, obtain `P3` for the product `B ×ˢ C`.
  have hBC : P3 (B ×ˢ C) :=
    P3_prod (X := Y) (Y := Z) (A := B) (B := C) hB hC
  -- Combine `hA` with `hBC` to get the desired result.
  simpa using
    (P3_prod (X := X) (Y := Y × Z) (A := A) (B := (B ×ˢ C)) hA hBC)