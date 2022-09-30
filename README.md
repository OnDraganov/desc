# DESC
DESC is a DErived Sheaf Calculator: a tool for working with (co)chains in derived categories of sheaves over finite posets. The supported operations include computing the minimal injective resolution of a constant sheaf and star/shriek pushforwards/pullbacks of injective (co)chains through monotonic maps. The code is based on [[1]](BrDr), where you can find all necessary theory as well as detailed description of the algorithms used.

## How to use

The main code is in the file `code/desc.py`. The `main()` method contains a sample code showing how to compute part of the examples presented in [[1]](BrDr), so it can be ran directly from terminal with `python3 code/desc.py`, but the recommended use is to create a jupyter notebook, and import `desc.py` in it.

## Remarks

We plan to soon add a jupyter notebook to the repository with several use-cases and interesting examples that can be computed with the tool -- it will serve both as a manual and as a demonstration of DESC.

## References
<a id="BrDr">[1]</a> 
Adam Brown and Ondřej Draganov.
Discrete Microlocal Morse Theory.
2022.
<https://arxiv.org/abs/2209.14993>




--------------------------------------------------

Copyright ©2022. Institute of Science and Technology Austria (IST Austria). All Rights Reserved.

This file is part of DESC: Derived Sheaf Calculator, which is free software: you can redistribute it and/or modify it under the terms of the MIT License.
 
This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the MIT License for more details.
 
You should have received a copy of the MIT License along with this program. If not, see <https://opensource.org/licenses/>.
