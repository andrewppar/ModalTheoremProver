<div id="table-of-contents">
<h2>Table of Contents</h2>
<div id="text-table-of-contents">
<ul>
<li><a href="#sec-1">1. The <code>main</code> Function</a>
<ul>
<li><a href="#sec-1-1">1.1. REPL</a></li>
</ul>
</li>
<li><a href="#sec-2">2. Formulas</a></li>
<li><a href="#sec-3">3. Canonical Representation of Formulas</a></li>
<li><a href="#sec-4">4. Propositional Theorem Prover</a></li>
<li><a href="#sec-5">5. Modal Theorem Prover</a>
<ul>
<li><a href="#sec-5-1">5.1. <code>proveK</code></a></li>
</ul>
</li>
</ul>
</div>
</div>


# The `main` Function<a id="sec-1" name="sec-1"></a>

We've written tests for a couple of the main features of the theorem prover. The `main` function runs all the tests in a verbose mode. For now, the theorem prover is meant to be used with a REPL, so different functions can be called and tested. When the guts of the theorem prover are done, we will use the `main` function to generate an interface for the user to decide which system they would like to use and input a formula to prove. It might also be nice to ask for an expected result and add that to our test cases. 

## REPL<a id="sec-1-1" name="sec-1-1"></a>

In order to use all of the functions, open up a REPL with GHC (or any other Haskell REPL): 

    andrew@Gentzen:~/Documents/haskell/modal-theorem-prover$ ghci
     GHCi, version 7.10.3: http://www.haskell.org/ghc/  :? for help
      Prelude>

Once there you can use `:load DepthFirstTheoremProver.hs` to load of the file. Then you'll have access to any function defined in DepthFirstTheoremProver.hs

# Formulas<a id="sec-2" name="sec-2"></a>

We take advantage of Haskell's strong typing to generate a `Formula` type. The type consistions of atomic formulas, negations, implications, conjunctions, disjunctions, possibilities, and necessities: 
-   AtomicFormula: a function from a string to an atomic formula, e.g. (AtomicFormula "The ground is wet")
-   Not: a function from a Formula to a Formula, e.g. (Not (AtomicFormula "It is Raining"))
-   Implies: a function from two formulas to a Formula, e.g. (Implies (AtomicFormula "Penny is dog") (AtomicFormula "Penny is a mammal"))
-   And: a function from a list of formulas to a Formula, e.g. (And [(AtomicFormula "p"), (Not (AtomicFormula "p"))]) &#x2013; a contradiction
-   Or: a function form a list of formulas to a Formula, e..g (Or [(AtomicFormula "p"), (Not (AtomicFormula "p"))]) &#x2013; a tautology (Sorry! I made this classical instead of constructive because constructive modal logic is not really well explored. When I get the chance to do some research into intuitionistic modal logics, I'll write that theorem prover.)
-   Possibly: A function from a Formula to a Formula, e.g. (Possibly (AtomicFormula "it is raining"))
-   Necessarily: A function from a Formula to a Formula, e.g. (Necessarily (Implies (AtomicFormula "A is a square") (AtomicFormula "A has four sides")))

# Canonical Representation of Formulas<a id="sec-3" name="sec-3"></a>

This function is responsible for removing all implications from formulas, pushing negations in as far as they can go, and ordering conjuncts and disjuncts in a canonical way. Ideally it would organize a formula in a way that is optimizes the therorem prover. We do not use Disjunctive Normal Form (DNF) for the formulas because we found empirically that it was slower. I think this is explained by the fact that a classical two sided sequent system *is* a way of making DNFs. So we end up redoing work in a much more complicated way if we convert a formula to DNF and then run it through the theorem prover. 

# Propositional Theorem Prover<a id="sec-4" name="sec-4"></a>

Since we needed the classical propositional rules for a logic, and because it's better for testing, we added a propositional theorem prover. The main entry point to this functionality is the function `propositionalProve :: Formula -> Bool`. To use this function at the REPL call `propositionalProve` of a Formula e.g. 

    *Main> propositionalProve (Implies (Implies (Implies (AtomicFormula "p") (AtomicFormula "q")) (AtomicFormula "p")) (AtomicFormula "p"))
    True

# Modal Theorem Prover<a id="sec-5" name="sec-5"></a>

Currently we only support proofs in System K. That's going to be updated soon with proofs from other modal systems. The cool thing about Tree Hypersequents is that you only really need on modal theorem prover &#x2013; the prover for system K. All of the rules for manipulating formulas themselves are the same throughout the various systems. This is a result from Francesca Poggiolesi

    @INCOLLECTION{Poggiolesi_TMTHFMPL_2009,
      AUTHOR={Francesca Poggiolesi},
      TITLE={The Method of Tree-Hypersequents for Modal Propositional Logic},
      BOOKTITLE={Towards Mathematical Philosophy},
      YEAR={2009},
      PUBLISHER={Springer},
      PAGES={31--51},
      VOLUME={28}
    }

## `proveK`<a id="sec-5-1" name="sec-5-1"></a>

The primary interface for proving formulas in System K is `proveK`. Here's an example: 

    *Main> proveK (Implies (Necessarily (Implies (AtomicFormula "p") (AtomicFormula "q"))) (Implies (Necessarily (AtomicFormula "p")) (Necessarily (AtomicFormula "q"))))
    True

<div id="footnotes">
<h2 class="footnotes">Footnotes: </h2>
<div id="text-footnotes">

<div class="footdef"><sup><a id="fn.1" name="fn.1" class="footnum" href="#fnr.1">1</a></sup> In my dissertation (see <https://andrewparisi.weebly.com/research.html>) I develop a proof system for modal logics that only uses lists of sequents as opposed to trees of sequents as the primary proof object. These are known as hypersequents. This project spun off of another one with some friends to develop a automated theorem prover for hypersequents. I had some questions as to whether hypersequents or tree hypersequents would be a more effective proof object when it comes to automated theorem proving. For more information about that project email me at <andrew.p.parisi@gmail.com>.</div>


</div>
</div>