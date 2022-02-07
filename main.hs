import PA1Helper
import System.Environment (getArgs)

-- Haskell representation of lambda expression
-- data Lexp = Atom String | Lambda String Lexp | Apply Lexp  Lexp 

-- Given a filename and function for reducing lambda expressions,
-- reduce all valid lambda expressions in the file and output results.
-- runProgram :: String -> (Lexp -> Lexp) -> IO ()

-- This is the identity function for the Lexp datatype, which is
-- used to illustrate pattern matching with the datatype. "_" was
-- used since I did not need to use bound variable. For your code,
-- however, you can replace "_" with an actual variable name so you
-- can use the bound variable. The "@" allows you to retain a variable
-- that represents the entire structure, while pattern matching on
-- components of the structure.
id' :: Lexp -> Lexp
id' v@(Atom _) = v
id' lexp@(Lambda _ _) = lexp
id' lexp@(Apply _ _) = lexp 

-- You will need to write a reducer that does something more than
-- return whatever it was given, of course!

------------------- GIVEN  --------------------
-- remove as filter application
remove :: (Eq a) => a -> [a] -> [a]
remove x = filter (\v -> v/=x)

-- Haskell representation of lambda expression
-- data Lexp = Atom String | Lambda String Lexp | Apply Lexp Lexp 
freevars :: Lexp -> [String]
freevars (Atom s)            = [s]
freevars (Lambda v e)        = remove v (freevars e)
freevars (Apply e1 e2)       = (freevars e1)++(freevars e2)

------------------------------------------------

{- ALPHA RENAMING
    concept: alpha rename every bound variable, left-to-right
    renames to 'a', then 'b', then 'c', etc.
-}

-- Iterates a character ('a' -> 'b', 'b' -> 'c', etc.).
iterChar :: Char -> Char
iterChar c = succ c

-- Determines what the next name would be after alpha-renaming the given Lexp.
nextName :: Char -> Lexp -> Char
nextName name v@(Atom a) = name
nextName name l@(Lambda v e) = iterChar(nextName name e) -- next name to use is iterated at each lambda
nextName name ap@(Apply e1 e2) = (nextName (nextName name e1) e2)

{- Performs alpha-renaming
   Char :: name indicates the name to replace any matching bound variable with (if in that mode)
   String :: renameThis - when == "!", the function is just recursing to the next lambda  
                          when != "!", it represents the name of each bound variable to be replaced with name
-}
aRename :: Char -> String -> Lexp -> Lexp
aRename name renameThis v@(Atom a) = if renameThis == a then Atom [name] -- perform a-renaming on this Atom to name
                                     else v -- this atom isn't being renamed

aRename name renameThis l@(Lambda v e) = 
    if renameThis == "!" then Lambda [name] (aRename (iterChar name) "!" (aRename name v e)) -- from \v.e: output here is \name.(e, but all instances of v replaced with name)
    else if renameThis == v then Lambda [name] (aRename name renameThis e) -- perform a-renaming on this Lambda's formal arg. to name
    else Lambda v (aRename name renameThis e) -- a lambda has been found at an outer scope, don't rename here but recurse further so any atoms can be renamed
    
aRename name renameThis l@(Apply e1 e2) = -- Continues the recursion on e1 and e2. 

    --It's possible that a-renaming has occurred within e1 by the time e2 is reached, so more names will be taken.
    --nextName accounts for this in case a-renaming will be performed in e2.
    if renameThis == "!" then Apply (aRename name renameThis e1) (aRename (nextName name e1) renameThis e2) 

    --we know what to rename, and only that will be renamed, so just keep recursing
    else Apply (aRename name renameThis e1) (aRename name renameThis e2)
       

{- BETA REDUCE
    concept: Apply (Lambda v e1) e2 
             Replace all occurences of v in e1 with e2
-}
bReduce :: Lexp -> Lexp -> Lexp -> Lexp
-- Case 1:   if \a.a b
bReduce replaceWith replaceThis v@(Atom a) = if v == replaceThis then replaceWith
                                             else v
-- Case 2:   if \a.b (\a.c d)
bReduce a1@(Atom a1v) a2@(Atom a2v) l@(Lambda v e) = if v == a1v then Lambda a1v (bReduce a1 a2 e)
                                                     else Lambda v (bReduce a1 a2 e)
-- Case 2.5: if \a.b (\c.d e) 
bReduce replaceWith replaceThis l@(Lambda v e) = if l == replaceThis then replaceWith
                                                 else Lambda v (bReduce replaceWith replaceThis e)
-- Case 3:   if (\a.a a) for example
bReduce replaceWith replaceThis a@(Apply l@(Lambda v e) e2) = if (bReduce e2 (Atom v) e) == replaceThis then replaceWith
                                                              else bReduce e2 (Atom v) (bReduce e2 (Atom v) e)
-- Case 4: break down our lexp further to match one of our previous cases
bReduce replaceWith replaceThis a@(Apply e1 e2) = if a == replaceThis then replaceWith
                                                  else Apply (bReduce replaceWith replaceThis e1) (bReduce replaceWith replaceThis e2)


{- ETA REDUCE
    given  : /a.(b c)
           : 1) if a == c, we can simplify to b
           : 2) if a is not free in b, we can simplify to b
           : 3) if no c, simplify to b
-}

-- helper function for finding a free variable
lambdaFound :: String -> [String] -> Bool
lambdaFound c s = elem c s

-- performs eta reducing
eReduce :: Lexp -> String -> Lexp -> Lexp -> Lexp
eReduce lexp a b c@(Atom v) =                                 -- eta reduction happens with a match of "a b c@(Atom v)"
    if (lambdaFound a (freevars b)) == False then b                 -- if a is NOT free in b, return b
    else lexp
eReduce lexp a b c = lexp                                     -- if in any other form, just return our lexp


-- find Lambda a(Apply b c) and reduce
eFind :: Lexp -> Lexp
eFind lexp@(Atom a) = lexp                                    -- base case return just atom
eFind lexp@(Lambda a (Apply b c))  = (eReduce lexp a b c)     -- attempt to eta reduce every time we come across a lambda (v e)
eFind lexp@(Lambda a b) = (Lambda a) (eFind b)                -- break down second part for match
eFind lexp@(Apply e1 e2) = Apply (eFind e1) (eFind e2)        -- break down the lexp further

-- Function used to call alpha rename -> beta reduction (until no longer possible) -> eta reduction (until no longer possible)
reducer1 :: String -> Lexp -> Lexp -> Lexp
reducer1 str prevInput lexp = if str == "alpha" then reducer1 "beta" (Atom "!") (aRename 'a' "!" lexp)
                              else if str == "beta" then if lexp == prevInput then reducer1 "eta" (Atom "!") lexp
                                                         else reducer1 "beta" lexp (bReduce (Atom "!") (Atom "!") lexp)
                              else if str == "eta" then if lexp == prevInput then lexp
                                                        else reducer1 "eta" lexp (eFind lexp)
                              else Atom "uh oh"

reducer :: Lexp -> Lexp
reducer lexp = reducer1 "alpha" (Atom "!") lexp

-- Entry point of program
main = do
    args <- getArgs
    let inFile = case args of { x:_ -> x; _ -> "input.lambda" }
    let outFile = case args of { x:y:_ -> y; _ -> "output.lambda"}
    -- id' simply returns its input, so runProgram will result
    -- in printing each lambda expression twice. 
    runProgram inFile outFile reducer
