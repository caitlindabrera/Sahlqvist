{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}
import qualified VsSahlq_proof4
import qualified Modal_syntax
import qualified Datatypes
import qualified SO_syntax

{- coq naturals to haskell Ints -}
c2hn :: Datatypes.Coq_nat -> Int
c2hn Datatypes.O = 0
c2hn (Datatypes.S n) = (c2hn n) + 1

{- Haskell Ints to Coq naturals -}
h2cn :: Int -> Datatypes.Coq_nat
h2cn 0 = Datatypes.O
h2cn n = Datatypes.S (h2cn (n-1))

-- propositional variables
p :: Int -> Modal_syntax.Modal
p n = Modal_syntax.Coq_atom (h2cn n)

-- conjunction
(/\) :: Modal_syntax.Modal -> Modal_syntax.Modal -> Modal_syntax.Modal
(/\) phi psi = Modal_syntax.Coq_mconj phi psi

-- disjunction
(\/) :: Modal_syntax.Modal -> Modal_syntax.Modal -> Modal_syntax.Modal
(\/) phi psi = Modal_syntax.Coq_mdisj phi psi

-- negation

neg :: Modal_syntax.Modal -> Modal_syntax.Modal
neg phi = Modal_syntax.Coq_mneg phi

-- implication
(-->) :: Modal_syntax.Modal -> Modal_syntax.Modal -> Modal_syntax.Modal
(-->) phi psi = Modal_syntax.Coq_mimpl phi psi

-- box
box :: Modal_syntax.Modal -> Modal_syntax.Modal
box phi = Modal_syntax.Coq_box phi

-- diamond
dia :: Modal_syntax.Modal -> Modal_syntax.Modal
dia phi = Modal_syntax.Coq_dia phi

instance Show SO_syntax.SecOrder where
  show (SO_syntax.Coq_predSO n m) = "[what is this?]"
  show (SO_syntax.Coq_relatSO n m) = "R(x" ++ (show (c2hn n)) ++ ", x" ++ (show (c2hn m)) ++ ")"
  show (SO_syntax.Coq_eqFO n m) = "(x" ++ (show (c2hn n)) ++ " = x" ++ (show (c2hn m)) ++ ")"
  show (SO_syntax.Coq_allFO n phi) = "(all x" ++ (show $ c2hn n) ++ "." ++ (show phi) ++ ")"
  show (SO_syntax.Coq_exFO n phi) = "(ex x" ++ (show $ c2hn n) ++ "." ++ (show phi) ++ ")"
  show (SO_syntax.Coq_negSO phi) = "(not " ++ (show phi) ++ ")"
  show (SO_syntax.Coq_conjSO phi psi) = "(" ++ (show phi) ++ "/\\" ++ (show psi) ++ ")"
  show (SO_syntax.Coq_disjSO phi psi) = "(" ++ (show phi) ++ "\\/" ++ (show psi) ++ ")"
  show (SO_syntax.Coq_implSO phi psi) = "(" ++ (show phi) ++ "-->" ++ (show psi) ++ ")"
  show (SO_syntax.Coq_allSO _ _) = "[shouldn't happen!]"
  show (SO_syntax.Coq_exSO _ _) = "[shouldn't happen!]"

corr :: Modal_syntax.Modal -> SO_syntax.SecOrder
corr phi = VsSahlq_proof4.vsSahlq_full_Modal phi
