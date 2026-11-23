# Guía Lean de Estabilidad de la transferencia mediante anfitriones

## Alcance de los enunciados formales

El preprint 1.1 usa los números de partición en cliques enteros y fraccionales sin restricción de orden de la Parte I. El desarrollo Lean demuestra en el grafo split original la estimación bilateral (1) del Teorema 1. Recibe un grafo residual, vecindades de anfitriones independientes en él y una asignación parcial propia sobre pares del núcleo. La cantidad de pares sin asignar es el cardinal del complemento de esta asignación dentro de los pares requeridos.

El Lema 4 carga cada sentido de la desigualdad a la capacidad libre del óptimo residual correspondiente. El Corolario 5 admite borrados arbitrarios de aristas cruzadas partiendo de una asignación completa, incluso cuando algún anfitrión queda aislado. La Proposición 6 acota el cambio de la brecha residual al modificar aristas sobre un núcleo fijo. Para la Proposición 7, la cota compilada usa el umbral del núcleo completo. El Corolario 8 acota la brecha sin restricción de orden por el doble de la suma de los excesos en los vértices. En el Teorema 9 la prueba formal parte de descomposiciones convexas finitas en emparejamientos admisibles y demuestra la cota de producto sin pesos y su comparación exponencial. El manuscrito obtiene esas descomposiciones mediante la caracterización del politopo de Edmonds.

## Reproducción

El repositorio oficial es <https://github.com/jtraverso/split-clique-partition-gap-ii>. Su README identifica las declaraciones Lean correspondientes. El archivo de fuentes distribuido con esta guía contiene el paquete en el directorio `lean`. Desde ese directorio se ejecutan los siguientes comandos con elan. La primera instalación requiere acceso a la red.

```sh
lake exe cache get
lake build SplitGapII SplitGapIIAudit
lake env lean SplitGapIIAudit.lean
lake env lean AllAxioms.lean
lake env lean SplitGapII11.lean
```

El paquete fija Lean 4.35.0-rc3 y la revisión de Mathlib indicada en el manifiesto de Lake. La primera auditoría imprime los axiomas de 25 declaraciones identificadas por su nombre. La segunda recorre los módulos importados del proyecto y rechaza todo teorema que use axiomas fuera de la extensionalidad proposicional, la elección clásica y la validez del cociente. El directorio de validación recoge la compilación limpia y la lista exhaustiva.


El archivo adicional SplitGapII11.lean comprueba las dos desigualdades de tamaños de listas y la aritmética del salto de dos unidades. Los dos programas exactos de la sección 3 certifican los óptimos de las tablas. Las demostraciones combinatorias de las proposiciones 5a y 6a, el umbral general por listas y las aplicaciones asintóticas se dan en el manuscrito.
