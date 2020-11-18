# Intuitionistic Theorem Prover!

## Intro

Welcome to the documentation for the Intuitionistic Theorem Checker. This can be used to check whether or not a particular formula is a theorem of intuitionistic logic. The primary way that this is done is by translating that formula in to the modal logic S4. The checker then tries to generate a hypersequent proof of the formula at each iteration that an application of proof rules does not result in a proof it attempts to generate a counter-example to the formula. This could take some time... but it. will give up after too much time. 


## Table of Contents
1. [Formulas](#forms)
2. [Usage](#main)

<a name="forms"></a>
## 1. Formulas

In order to use the theorem checker it's important to pass it well-formed formulas otherwise it will not know what to do with them. Formulas are written in prefix notation (sorry it's WAY easier for a computer to work with). So if 'p' is a formula so is (Not p). Here's the full syntax: 

 - if s is a STRING then (AtomicFormula s) is a formula
 - if p is a formula then (Not p) is a formula
 - if conjuncts is a list of formulas (e.g. [(AtomicFormula "p"), (AtomicFormula "q")]) then (And conjuncts) is a formula
 - if disjuncts is a list of formulas then (Or disjuncts) is a formula
 - if p and q are formulas then (Implies p q) is a formula
 - if p and q are formulas then (Equivalent p q) are formulas
 
<a name="main"></a>
## 2. Usage

Clone this repo: 
```
git@github.com:andrewppar/ModalTheoremProver.git
```

You'll have to have ghc installed if you want to compile the binary yourself. This can be done with the command 

```make main``` 

in the root of the repo. Alternatively, the most up  to date binary is included in the repo. 

In order to see whether or not a formula is provable or has a counterexample pass a formula to the Main module. 

For example: 
```
./ModalTheoremProver/Main '(Not (AtomicFormula "p"))' 
```

will result in CounterExample because there is a counter example to the formula (Not (AtomicFormula "p")) has as counter-example. 

In addition to seeing whether or not a formula is a theorem you can see the /justification/ for why it's a theorem. This can be done by passing the '-s' flag to the Main function, e.g. 

```
./ModalTheoremProver/Main -s '(Not (AtomicFormula "p"))' 
```

This will print a model like so 
```
Right Worlds:
 0 |= ["p"]|/= []

Relations:
```
In this case a model with a single world that makes (AtomicFormula "p") true is a counter example to the above formula.


