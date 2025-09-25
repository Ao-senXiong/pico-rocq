## Known Workable Versions with coq

- coq 8.20.0

## Dependency required

- coq-record-update 0.3.4 https://github.com/tchajed/coq-record-update

## How to Build the Project

1. Generate the Makefile:
   ```sh
   coq_makefile -f _CoqProject -o Makefile
   ```
2. Build the project:
   ```sh
   make
   ```
## Ideas on refactoring

1. Remove cname and just use the indice. This will simpfy the encoding of wf_class_table.
2. Define explict object type and simpfy the wf_class, method and constructor.
3. Define seperate runtime qualifier and use tyable relation between runtime qualifier and static type instead. It is somehow hacky to do what I am doing now for lost. [fixed]
4. This proof currently is on relationship big-step semantics, there were also functional big-step semantics, pretty big-step semantics and coinductive big-step semantics.
5. learning: fixpoint and inductive's proof
6. learnng: projectection is hard and bad.
7. learning: complex case analysis (more than 600 cases).
8. doing induction over the evaluation rule if there is subterm
