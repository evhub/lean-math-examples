namespace ctx
    @[inline, reducible] def pipe {A B: Sort _} (a: A) (f: A → B): B := f a
    infix ` ↦ `:50 := pipe

    def of {A B X: Sort _} (f: A → B): A → (B → X) → X :=
        λ a: A,
        λ ctx: B → X,
        a ↦ f ↦ ctx

    def dne {A X: Sort _} (nna: (A → X) → X) (ctx: A → X): X :=
        nna ctx

    inductive or (A: Sort _) (B: Sort _)
    | inl (a: A) : or
    | inr (b: B) : or

    def lem {A X: Sort _} (ctx: (or A (A → X)) → X): X :=
        begin
            apply ctx,
            apply or.inr,
            intro,
            apply ctx,
            apply or.inl,
            assumption,
        end

    def of_sum {A B: Sort _} (ab: A ⊕ B): or A B :=
        begin
            cases ab,
            case sum.inl {
                apply or.inl,
                assumption,
            },
            case sum.inr {
                apply or.inr,
                assumption,
            },
        end

    def of_neg {A X: Sort _} (na: A → false): A → X :=
        begin
            intros,
            apply false.elim,
            apply na,
            assumption,
        end
end ctx
