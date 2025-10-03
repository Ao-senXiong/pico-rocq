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
