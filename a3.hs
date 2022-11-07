-- CISC 360 a3, Fall 2022

-- SEE THE FILE a3.pdf
-- for instructions

module A3
where
import Data.List

-- Q1:
-- Add your student ID (if in a group of 2, write the second student's ID in a comment):
student_id :: Integer
student_id = 20226046

-- THIS FILE WILL NOT COMPILE UNTIL YOU ADD YOUR STUDENT ID ABOVE.

{-
Q2: Truth Tables

To build a truth table for a formula, there are 4 steps:

  1) Traverse the formula to find all atomic propositions (propositional variables).

  2) Find all the possible valuations---combinations of True and False
      for the atomic propositions in the formula.

  3) Evaluate the formula for each valuation obtained in (2).

  4) Use the results of (1-3) to build the table.

In this question, you will implement steps (1-3).
-}

-- Variable is a synonym for String.
type Variable = String

-- In our simplified version of classical propositional logic,
-- we have the following definition for a Formula:
data Formula = Top                      -- truth (always true)
             | Bot                      -- falsehood (contradiction) (not used in Q3)
             | And Formula Formula      -- conjunction
             | Or Formula Formula       -- disjunction
             | Implies Formula Formula  -- implication
             | Iff Formula Formula      -- if and only if (equivalence) (not used in Q3)
             | Not Formula              -- negation (not used in Q3)
             | Atom Variable            -- atomic proposition ("propositional variable")
             deriving (Eq, Show)

-- Some atoms, for convenience
vA = Atom "A"
vB = Atom "B"
vC = Atom "C"
vD = Atom "D"
vE = Atom "E"
vF = Atom "F"

-- Some example formulas that you can use to test your functions
formula1  = Implies (And vA vB) vC
formula2  = Implies Bot (And vA vB)
formula3  = Implies (And vA vB) Top
formula4  = And (Implies vA (And vB vC)) (And vD vE)
formula5  = And vA vB
formula6  = Not vA
formula7  = Implies vA vB
formula8  = Or vA (Not vA)
formula9  = Or vA (Not vB)

formula10 = Iff (And vC vB) (And vB vC)
formula11 = Iff Top vA


-- A Valuation is a list of pairs corresponding to a truth value (i.e. True or False)
--  for each atom in a formula
type Valuation = [(Variable, Bool)]

-- A TruthTable is an enumeration of the valuations for a given formula,
-- with each valuation paired with the corresponding evaluation of that formula.
-- (This corresponds to a truth table with no "intermediate columns".)
data TruthTable = TruthTable [(Valuation, Bool)]

{-
   This function is here so that when you print a TruthTable in GHCi, the table is nice and readable.
   You don't need to understand how this works to complete the assignment.
-}
instance Show TruthTable where
  show (TruthTable rows) =
    case rows of
      [] -> ""
      ([], result) : _ -> "   result is " ++ pad_show result ++ "\n"
      ((c,b) : valu, result) : xs -> 
        c ++ "=" ++ (pad_show b) ++ "   "
          ++ show (TruthTable [(valu,result)])
          ++ show (TruthTable xs)
    where
      pad_show True  = "True "
      pad_show False = "False"

{-
  Q2a: getAtoms:

  Traverse a formula and build a list of all Atoms in the formula, without duplicates.

  You may use the built-in function "nub", which takes a list and returns the list
  without duplicates.
-}
getAtoms :: Formula -> [Variable]

getAtoms Top               = []
getAtoms Bot               = []

getAtoms (Atom v)          = [v]

getAtoms (Not phi)         = getAtoms phi
getAtoms (And phi1 phi2)   = nub(getAtoms phi1 ++ getAtoms phi2)
getAtoms (Or phi1 phi2)    = nub(getAtoms phi1 ++ getAtoms phi2)
getAtoms (Iff phi1 phi2)   = nub(getAtoms phi1 ++ getAtoms phi2)
getAtoms (Implies phi psi) = nub(getAtoms phi ++ getAtoms psi)

{-
   Q2b: getValuations:

   Build a list of all possible valuations for a set of atomic propositions
-}
getValuations :: [Variable] -> [Valuation]
getValuations []       = [[]]
getValuations (c : cs) = map (\e -> [(c,True)]) cs

{-
where 1 variable exists 
[[(c,True)],[(c,False)]]

-}

{-
  Hint: To apply a function f to every element of a list xs,
   write  map f xs.
  For example, the following adds 1 to the start of every list
   in a list of lists [[2,3], [2,4]]:
   map (\ys -> 1 : ys) [[2,3], [2,4]]  ==  [[1,2,3], [1,2,4]]
-}

{-
   Q2c: evalF:
    Evaluate a formula with a particular valuation,
     returning the resulting boolean value
-}
evalF :: Valuation -> Formula -> Bool
evalF valu formula =
    case formula of
        Top               -> True
        Bot               -> False
        Not phi1          -> not (evalF valu phi1)
        Implies phi1 phi2 -> not (evalF valu phi1) || (evalF valu phi2)
        Atom c            -> undefined
        And phi1 phi2     -> undefined
        Or phi1 phi2      -> undefined
        Iff phi1 phi2     -> undefined

-- buildTable:
--  Build a truth table for a given formula.
--  You can use this function to help check your definitions
--  of getAtoms, getValuations and evalF.
buildTable :: Formula -> TruthTable
buildTable psi =
  let valuations = getValuations (getAtoms psi)
  in
    TruthTable (zip valuations
                    (map (\valu -> evalF valu psi) valuations))


{-
Q3: Tiny Theorem Prover

    This question asks you to complete an implementation of a
    continuation-based backtracking theorem prover that follows the rules
    given in a3.pdf.
 
    The prover is structured using two functions that do all the work,
    and one function that "kicks off" the process by passing continuations:

       prove'      looks at the goal formula (the formula we're trying to prove),
                     trying the -Right rules;
 
       prove_left  looks at the assumptions, trying the -Left rules;

       prove_all   calls prove', collecting all solutions.

    [X] Use-Assumption
    [ ] Top-Right
    [X] Implies-Right
    [ ] And-Right
    [ ] Or-Right-1 and Or-Right-2
    
    [X] Implies-Left
    [ ] And-Left
    [ ] Or-Left

    You do not need to handle Bot, Not, and Iff formulas in this question.
-}

-- a Context is a list of Formulas, representing assumptions
type Context = [Formula]

{- A Derivation represents the rules used to construct a proof.

   For example, if we prove

    [vB] |- (And vB Top)
     
   by using UseAssumption to prove vB, TopRight to prove Top, and then AndRight,
   the Derivation would be

     AndRight (UseAssumption vB) TopRight

   As a tree, drawn the way computer scientists usually draw it, this looks like

               AndRight
              /        \
       UseAssumption   TopRight
            vB

   But it's easier to see the connection to the rules if we draw the root at the bottom:

            vB                        ---------- UseAssumption       ----------- TopRight
       UseAssumption   TopRight       [vB] |- vB                     [vB] |- Top
              \        /              --------------------------------------------------- AndRight
               AndRight                               [vB] |- And vB Top

The arguments to a Derivation constructor represent the premises used,
or for UseAssumption, the assumption formula being used.

OrRight takes an extra first argument indicating whether rule OrRight-1 or OrRight-2
was used.

For example,

   [OrRight 2 (UseAssumption vB)]

should be returned by

   prove_all [vB] (Or vA vB)

-}
data Derivation = UseAssumption Formula
                | TopRight
                | ImpliesRight Derivation
                | AndRight Derivation Derivation
                | ImpliesLeft Derivation Derivation
                | AndLeft Derivation
                | OrLeft Derivation Derivation
                | OrRight Int Derivation
                deriving (Show, Eq)

{-
  prove': Given a context, a formula, and two continuations representing success and failure,
          call the appropriate continuation.
-}
prove' :: Context         -- formulas being assumed (to the left of the turnstile  |-  )
       -> Formula         -- goal formula to be proved (to the right of the turnstile)
       -> (Derivation -> (() -> b) -> b,
                          -- kSucceed: call this if we proved the formula,
                          --    with the constructed Derivation and a function to call to get more proofs
           () -> b)       -- kFail: call this if we can't prove the formula
       -> b

prove' ctx goal (kSucceed, kFail) =
  let try_prove_left () = prove_left ctx ([], ctx) goal (kSucceed, kFail)
      try_right_rules () =
           case goal of
                Top               -> -- Top-Right rule
                     undefined

                Implies phi psi   -> -- Implies-Right rule
                     prove' (phi : ctx)
                            psi
                            (\deriv -> \more ->
                                 kSucceed (ImpliesRight deriv) more,
                             try_prove_left)

                And phi1 phi2     -> -- And-Right rule
                     undefined

                Or phi1 phi2      -> -- Or-Right rules (try Or-Right-1, if it fails, try Or-Right-2)
                     undefined

                _                 -> -- Can't use any of the -Right rules, so:
                     try_prove_left ()
  in
    if elem goal ctx then  -- Use-Assumption rule
      kSucceed (UseAssumption goal) try_right_rules
    else
      try_right_rules ()

{-
  prove_left: Given an original context,
                    a context that prove_left has already processed,
                    a context that prove_left has not processed,
                    a goal formula,
                    and two continuations,
                    call the appropriate continuation.
-}
prove_left :: Context              -- the original context
           -> (Context, Context)   -- the "done" context, and the "to do" context
           -> Formula              -- the goal formula
           -> (Derivation -> (() -> b) -> b,            -- kSucceed: call this if we proved the formula
               () -> b)            -- kFail: call this if we can't prove the formula
           -> b
           
prove_left original (done, []) goal (kSucceed, kFail) =
                       --  ^^ the "to do" context is empty, so there's nothing remaining to examine
    if original == done then
        -- prove_left looked at everything but didn't change the context at all, so fail
        kFail ()
    else
        -- prove_left changed something, so we are giving prove' stronger assumptions
        prove' done goal (kSucceed, kFail)
        
prove_left original (done, focus : rest) goal (kSucceed, kFail) =

    let leave_alone () =   -- leave_alone: Call this to move "focus", the head of the to-do list,
                           --              into the "done" list without changing "focus"
            prove_left original (done ++ [focus], rest) goal (kSucceed, kFail)
    in
      case focus of
        Implies phi1 phi2 ->   -- Implies-Left rule
            prove' (done ++ rest) phi1 (-- kSucceed:
                                        \deriv1 -> \more1 ->
                                             prove' (done ++ [phi2] ++ rest)
                                                    goal
                                                    (\deriv2 -> \more2 ->
                                                        kSucceed (ImpliesLeft deriv1 deriv2) more2,
                                                     more1),
                                        -- kFail:
                                        leave_alone)
        
        And phi1 phi2 ->       -- And-Left rule
            undefined
        
        Or phi1 phi2 ->        -- Or-Left rule
            undefined
        
        focus -> leave_alone ()


{-
  prove_all: Given a context and a formula,
             collect all possible derivations that prove the formula (according to the rules given in a3.pdf).
-}
prove_all :: Context -> Formula -> [Derivation]
prove_all ctx goal = prove' ctx goal (\deriv -> \more -> deriv : (more ()),
                                      \() -> [])

{-
  prove: Given a context and a formula,
         return True if the formula is provable using the rules given in a3.pdf,
            and False otherwise.
-}
prove :: Context -> Formula -> Bool
prove ctx goal = prove' ctx goal (\deriv -> \more -> True,
                                  \() -> False)


test_imp1 = prove [Implies vB vC] (Implies vB vC)
test_imp2 = prove [Implies vB vC] (Implies (And vB vB) vC)
test_imp3 = not (prove [Implies (And vB vD) vC] (Implies vB vC))

test_imps = test_imp1 && test_imp2 && test_imp3

test_or1 = prove [Or vA vB] (Or vB vA)
test_or2 = prove [Or vC (And vA (Implies vA vB))] (Or vB vC)
test_or3 = prove [vA, Or (Implies vA vB) (Implies vA vC)] (Or vB (Or vB vC))
test_or4 = not (prove [Or vC (And vA (Implies vA vD))] (Or vB vC))
test_or5 = elem (OrRight 1 (UseAssumption vB)) (prove_all [vA, vB] (Or vB vA))
        && elem (OrRight 2 (UseAssumption vA)) (prove_all [vA, vB] (Or vB vA))
test_ors = test_or1 && test_or2 && test_or3 && test_or4 && test_or5

