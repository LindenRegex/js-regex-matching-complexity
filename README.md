# Proving that JavaScript regex matching is OptP-complete

## Setup

1. Create an empty Opam switch:

   ```
   opam switch create . --empty
   ```

2. Pin the version of Warblre:

   ```
   opam pin add warblre.0.1.0 https://github.com/epfl-systemf/Warblre.git#a1ffc3f2e47d942ad9e1194dfb71f0783ead6d8a
   ```

3. Pin the version of Linden:

   ```
   opam pin add linden https://github.com/epfl-systemf/Linden.git#popl26_artifact
   ```

4. Run `eval $(opam env)`.