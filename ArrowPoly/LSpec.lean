import Lean

-- adapted from https://github.com/yatima-inc/LSpec

/--
A variant of `Decidable` for tests. In the failing case, gives an explanatory message.
-/
class inductive TDecidable (p : Prop) where
  | isFalse (h : ¬ p) (msg : Std.Format) : TDecidable p
  | isTrue  (h : p) : TDecidable p

instance (priority := low) (p : Prop) [d : Decidable p] : TDecidable p :=
  match d with
  | isFalse h => .isFalse h f!"Evaluated to false"
  | isTrue h => .isTrue h

/-
instance (priority := low) (p : Prop) [d : TDecidable p] : Decidable p :=
  match d with
  | .isFalse h _ => isFalse h
  | .isTrue h => isTrue h
-/

def create_binary_error (m : String) (x y : α) [Repr α] : Std.Format :=
  m ++
  (repr x).indentD ++
  Std.Format.line ++ "and" ++
  (repr y).indentD
-- s!"{m}{(repr x).indentD}\nand\n{(repr y).indentD}"

instance (priority := low) TDecidable.equal (x y : α) [DecidableEq α] [Repr α] : TDecidable (x = y) :=
  if h : x = y then
    .isTrue h
  else
    .isFalse h <| create_binary_error "Expected to be equal:" x y

instance (x y : α) [BEq α] [Repr α] : TDecidable (x == y) :=
  if h : x == y then
    .isTrue h
  else
    .isFalse h <| create_binary_error "Expected to be equal:" x y

instance (x y : α) [DecidableEq α] [Repr α] : TDecidable (x ≠ y) :=
  if h : x ≠ y then
    .isTrue h
  else
    .isFalse h <| "Both equal to:" ++ (repr x).indentD

instance (x y : α) [BEq α] [Repr α] : TDecidable (x != y) :=
  if h : x != y then
    .isTrue h
  else
    .isFalse h <| "Both equal to:" ++ (repr x).indentD

instance Nat.tdecidable_forall_lt (b : Nat) (p : Nat → Prop) [d : (n : Nat) → TDecidable (p n)] :
  TDecidable (∀ n, n < b → p n) :=
match b with
| 0 => .isTrue (by simp [Nat.not_lt_zero])
| b+1 =>
  match tdecidable_forall_lt b p with
  | .isTrue h =>
    match d b with
    | .isTrue hb =>
      .isTrue $ by
        intros n hn
        cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hn) with
        | inl hl => cases hl; assumption
        | inr => apply h; assumption
    | .isFalse hb msg =>
      .isFalse (λ h => hb (h _ (Nat.lt_succ_self _))) <|
        f!"Fails on input {b}. " ++ msg
  | .isFalse h msg => .isFalse (λ h' => h λ n hn => h' _ (Nat.le_step hn)) msg

/-- 
The basic structure used to encode a specification.
-/
inductive LSpecTest
  | prop (descr : String) (p : Prop) (h : TDecidable p)

/-- 
`test` is a single basic test.
-/
def test (descr : String) (p : Prop) [TDecidable p] :=
  LSpecTest.prop descr p inferInstance

/-- 
Prints the result of a test.
-/
def printMsg : String × Bool × Std.Format → String
  | (d, b, msg) =>
    let head := if b then s!"✓ {d}" else s!"× {d}"
    match msg with
    | .nil => head
    | _ => head ++ msg.indentD.pretty

/--
The LSpec monad, records tests and whether they passed, along with an optional additional message.
-/
abbrev LSpec := StateT (List (String × Bool × Std.Format)) Id Unit

def LSpec.addResult (desc : String) (b : Bool) (msg : Std.Format) : LSpec :=
  StateT.modifyGet (λ s => ((), (desc, b, msg) :: s))

instance : Coe LSpecTest LSpec where
  coe := fun
    | LSpecTest.prop d _ h =>
      match h with
      | .isTrue _ => LSpec.addResult d true Std.Format.nil
      | .isFalse _ msg => LSpec.addResult d false msg

/--
Runs a set of `LSpec` tests and appends the results to 
another list of results (given as input by the caller).
-/
def LSpec.run (tests : LSpec) : List (String × Bool × Lean.Format) :=
  (StateT.run tests []).2.reverse

/--
Generates a report for all the results in a `LSpec` test,
returning `true` if all tests passed and `false` otherwise.
-/
def LSpec.runAndCompile (t : LSpec) : Bool × String :=
  let res := t.run
  (res.foldl (init := true) fun acc (_, r, _) => acc && r,
    "\n".intercalate <| res.map printMsg)

def LSpec.toIO (t : LSpec) : IO Unit := do
  let (success?, msg) := t.runAndCompile
  IO.eprintln msg
  if success? then
    IO.eprintln "All tests succeeded"
  else
    throw <| IO.userError "A test failed"

instance : Coe LSpec (IO Unit) := ⟨LSpec.toIO⟩

/-- 
Runs a `LSpec` test suite and pretty prints the results.
-/
def lspec (s : String) (t : LSpec) : IO Unit := do
  IO.println s!"Testing: {s}"
  t

macro "#lspec " term:term : command =>
  `(#eval (LSpec.toIO $term))

/--
Testing using `#lspec` with something of type `LSpec`.
-/
private def test1 : LSpec := do
  test "Nat equality" <| 4 = 4
  test "Nat inequality" <| 4 ≠ 5
  test "bool equality" <| 42 == 42
  test "list length" <| [42].length = 1
  test "list nonempty" <| ¬ [42].isEmpty

#lspec test1

#eval lspec "running tests" test1

/--
Testing using `#lspec` with something of type `LSpecTest`.
-/
private def test2 := test "true" <| true

#lspec test2

#lspec test "true" <| true

#lspec do
  test "a" <| 4 = 4
  test "b" <| 4 ≠ 5

#lspec test "all lt" <| ∀ n, n < 5 → n - 10 = 0

#lspec test "all sum lt" <| ∀ n, n < 5 → ∀ m, m < 5 → n + m < 9
