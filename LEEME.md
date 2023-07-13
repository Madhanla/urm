## Librería complementaria al Trabajo de Fin de Grado
### Implementación de la máquina URM y variantes
Autor: Martín Torres Valverde (UGR, Grado en Matemáticas, curso
2022/2023)

Para instalarla hay que intentar con `cabal build`.

#### Módulos principales
1. `Data.URM` -- Aquí se define la máquina de registros ilimitados y
   se ponen un par de ejemplos que aparecen en el texto.
2. `Data.URM.ZURM` -- Aquí se define la variante ZURM que trabaja con
   números enteros; se demuestra la ZURM-computabilidad de beth y su
   inversa como están definidas en el texto.
3. `Data.PRF.PRFExt` -- Aquí se definen las funciones recursivas
   parciales de una forma extensible.
4. `Data.PRF.Funciones` y `Data.PRF.Operaciones` -- Aquí se muestran
   algunas funciones y operaciones que se han demostrado recursivas en
   el texto.
5. `Data.URM.PRF` -- Aquí se muestra un método para obtener la URM que
   computa una función parcial recursiva dada. 

   ____________________________________________ Otros módulos son de
   menos interés en lo que respecta al trabajo. Por ejemplo, los
   módulos `Data.PRF.Rapidas` y `Data.PRF.Rapidas.Funciones` son un
   intento de mejorar la eficiencia de las funciones recursivas
   parciales usando sumas y productos reales (no definidos por
   recursión). Mientras que `Data.PRF.Lang` busca ayudar en la
   escritura del lenguaje extensible del módulo `Data.PRF.PRFExt`.  A
   su vez, `Data.PRF.Clases` define ciertas clases útiles para pasar
   de unas extensiones del lenguaje a otras. 
   
   Este segundo tipo de módulos es más experimental.
