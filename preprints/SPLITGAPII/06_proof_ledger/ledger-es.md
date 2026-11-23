# Guía de las demostraciones de *Estabilidad de la brecha de partición en cliques en grafos split*

## 1. De la carga de las aristas a la puntuación de una clique del núcleo

En una presentación split, $V$ es la clique y $H$ es independiente. Un grafo $B$ sobre $V$ marca las aristas residuales. Cada par restante del núcleo pertenece a $J$ y puede formar un triángulo con anfitrión. Una asignación designa un anfitrión adyacente a ambos extremos. Los pares asignados a un mismo anfitrión deben formar un emparejamiento para que los triángulos tengan aristas cruzadas distintas.

En una partición fraccional fijemos una arista $e$. Su carga total es uno. Sumemos esta igualdad sobre las aristas, invirtamos el orden de las dos sumas finitas y contemos cuántas veces aparece cada peso $x_K$. Aparece una vez por cada arista de $K$.

$$
\sum_{e\in E(G)}1=\sum_e\sum_{K\supseteq e}x_K=\sum_K\binom{|K|}{2}x_K.
$$

El primer miembro es el coste de usar una pieza por arista. Restamos el coste de la partición elegida. Por ejemplo, un término con $|K|=3$ y $x_K=1/2$ aporta $3/2-1/2=1$ unidad de ahorro.

$$
|E(G)|-\sum_Kx_K=\sum_K\left(\binom{|K|}{2}-1\right)x_K.
$$

Para una pieza $Q$ del núcleo, sean $a=\binom{|Q|}{2}$ y $j=|J\cap\binom Q2|$. Hay $a-j$ aristas residuales. Un triángulo con anfitrión reemplaza tres aristas individuales por una pieza y ahorra dos. Ocupar los $j$ pares requeridos desplaza así un ahorro potencial de $2j$. Se obtienen las dos expresiones de la puntuación y la identidad (3).

$$
w(Q)=(a-1)-2j=2(a-j)-a-1=2e_B(Q)-a-1.
$$

## 2. Por qué la asignación completa da una igualdad (Lema 2)

Una pieza con anfitrión no puede contener un segundo anfitrión. Si contiene $u$ vértices del núcleo, sus $\binom u2$ pares pertenecen a $J$, pues su vecindad es independiente en $B$. Comparemos las dos unidades por par requerido con el ahorro que dan las aristas de la pieza.

$$
2\binom u2-\left(\binom u2+u-1\right)=\binom u2-u+1=\frac{(u-1)(u-2)}2.
$$

Para $u=1,2,3,4$ las cantidades disponibles son $0,2,6,12$ y los ahorros reales son $0,2,5,9$, respectivamente. La primera desigualdad estricta aparece en $u=3$. Al sumar, cada pieza del núcleo aporta su puntuación más dos por par requerido ocupado. Cada pieza con anfitrión aporta a lo sumo dos por tal par. El total imputado a un par es a lo sumo dos porque su carga total es uno. La suma de puntuaciones del núcleo es a lo sumo el óptimo residual, que aquí denotamos por $P$ para cualquiera de los dos problemas.

Para alcanzar la cota, partimos de un empaquetamiento residual óptimo $y$. Para cada par requerido $e$, sea $\ell_e$ su carga en $y$. Su triángulo designado recibe peso $1-\ell_e$. La asignación propia protege las dos aristas cruzadas de cada triángulo designado. Completamos las capacidades restantes con aristas individuales. Los pesos son enteros cuando $y$ es entero. Las dos contribuciones al ahorro se suman así.

$$
\begin{aligned}
S_{\rm core}&=P+2\sum_{e\in J}\ell_e,\\
S_{\rm host}&=2\sum_{e\in J}(1-\ell_e),\\
S_{\rm core}+S_{\rm host}&=P+2|J|.
\end{aligned}
$$

Al restar esta suma de $|E(G)|$ obtenemos las dos igualdades de (2). Al restarlas entre sí, el término de referencia se cancela y queda la brecha $F(B)-I(B)$.

## 3. Pares sin asignar y los dos sentidos del error

Para el Lema 3, intersecamos cada clique del grafo mayor con los vértices del subgrafo inducido. Las aristas conservadas mantienen carga uno. En sentido inverso, una partición de las aristas eliminadas en $p$ piezas extiende cualquiera de los óptimos a un coste adicional de a lo sumo $p$. Ambos incrementos están en $[0,p]$, por lo que su diferencia tiene valor absoluto a lo sumo $p$.

En el Teorema 1 un vértice privado de grado dos completa cada uno de los $L$ pares sin asignar. El par ya era una arista del núcleo. Al eliminar los nuevos vértices desaparecen exactamente $2L$ aristas cruzadas, que pueden reponerse individualmente en la cota de restricción. El grafo completado tiene brecha $\Phi(B)=F(B)-I(B)$ por el Lema 2.

El Lema 4 también se comprueba en el grafo original. Pongamos $M=J\setminus J_0$, $A=|E(G)|-2|J|$. Por los triángulos ausentes se pierden $R=2\sum_{e\in M}(1-\ell_e)$ unidades de ahorro en la construcción de la sección 2 de esta guía. El coste de cada problema está entonces entre $A-P$ y $A-P+R$. Para la primera cota restamos el extremo superior fraccional del inferior entero. Para la segunda elegimos los extremos contrarios.

$$
\begin{aligned}
(A-I)-(A-F+R_F)&=F-I-R_F,\\
(A-I+R_I)-(A-F)&=F-I+R_I.
\end{aligned}
$$

## 4. Borrados, igualdad y protección de las asignaciones

En el Corolario 5 cada triángulo perdido contiene una arista cruzada borrada. Como los triángulos originales son disjuntos en aristas, elegir una de ellas por triángulo perdido da una inyección en los borrados. Así $L\le q$, lo que demuestra (6). La Proposición 6 trata otra operación. Añadir una arista residual aumenta la puntuación de cada empaquetamiento fijo en dos veces su carga en esa arista. Ambos incrementos óptimos están en $[0,2]$, de modo que su diferencia cambia en valor absoluto a lo sumo dos. Iterando se obtiene (7).

El ejemplo de doce vértices da sucesivamente las brechas $10-10=0$, $11-10=1$ y $11-11=0$. Para la optimalidad usamos la Proposición 5a. Incorporar el par $14$ al residual restablece una asignación completa para calcular los valores exactos después del borrado. Los términos de referencia y los óptimos dan

$$
\begin{aligned}
(28-11)-(28-35/3)&=2/3,\\
(29-11)-(29-41/3)&=8/3,\\
8/3-2/3&=2.
\end{aligned}
$$

Los dos verificadores finitos de la edición comprueban cada capacidad para el empaquetamiento fraccional y cada subconjunto del núcleo para los precios duales. La coincidencia de los valores primal y dual certifica el óptimo fraccional. La recurrencia entera elige una clique disponible de puntuación positiva y retira sus pares, o termina con valor cero. Termina porque cada clique elegida elimina al menos un par. Manteniendo fijo el residual original, el borrado en $14$ deja $L=1$ y también da igualdad en (1).

En la Proposición 6a, sea $b=\lfloor(v+r)/2\rfloor$. Cada extremo de un par mixto excluye a lo sumo $b$ anfitriones, así que en su familia quedan al menos $w+v+r-2b\ge w$ por lista. Galvin colorea cada grafo bipartito de solicitudes, de grado máximo a lo sumo $w$. Las tres familias son disjuntas. En cada vértice de $W$ ya se usaron a lo sumo $v$ anfitriones. Para un par interno sumamos las exclusiones de ambos extremos y las restamos de la reserva completa.

$$
3(w+v+r)-2b-2v\ \ge\ 3(w+v+r)-(v+r)-2v=3w+2r\ge w.
$$

Häggkvist–Janssen colorea por tanto los pares internos sin reutilizar aristas cruzadas. Sólo pueden perderse triángulos asignados antiguos. Antes del borrado se aplica (2) y después (1), con el mismo residual en ambos casos, y se obtiene la cota $2q_0$. En los ejemplos con relleno quedan al menos $n/25-4$ anfitriones de relleno disponibles. Para todo $n$ suficientemente grande esta cantidad supera $3\lfloor n/100\rfloor$. Redistribuirlos proporciona las tres familias ampliadas sin cambiar el orden. Elegir $b$ borrados en cada uno de los $w$ vértices de relleno protege los triángulos antiguos y permite $wb=\Theta(n^2)$ borrados.

## 5. Cómo se deducen las cotas de recuperación de las vecindades restantes

En la Proposición 7, una arista $e$ a cuya lista le faltan $d_k(e)$ colores recibe los auxiliares numerados desde uno hasta $d_k(e)$. Cada lista tiene así al menos $k$ colores. Después de una coloración propia, las aristas con el color auxiliar $t$ forman un emparejamiento de $D_t^{(k)}$. Su número es a lo sumo el número de emparejamiento de ese grafo. Cada arista descartada tiene un solo color y la suma la cuenta una vez. El Teorema 1 convierte la cantidad de pares sin asignar en (8).

En el Corolario 8 tomamos el residual vacío. Todas las puntuaciones residuales son negativas y el empaquetamiento vacío da $F=I=0$. Si $|H|\ge2c$, sea $s_u=(|M_u|-\lfloor c/2\rfloor)_+$, donde $M_u$ es el conjunto de anfitriones omitidos por $u$. La lista de $uv$ tiene tamaño al menos $|H|-|M_u|-|M_v|\ge c-s_u-s_v$. Bastan por tanto conjuntos privados de $s_u$ y $s_v$ colores auxiliares para esta arista. Cada color privado sólo se usa en su propio vértice, luego aparece en a lo sumo una arista. Resulta $\Delta(G)\le2\sum_u s_u$. Si todos los excesos son cero, la brecha se anula incluso con muchas omisiones.

En el Teorema 9 elegimos en cada anfitrión un emparejamiento según una descomposición convexa de su emparejamiento fraccional. La probabilidad de que $e$ falte en todos los anfitriones se factoriza por independencia. Eliminar las asignaciones duplicadas no cambia los pares sin cubrir. La asignación resultante satisface el Lema 4 en cada resultado, así que al tomar esperanzas cada indicador de par ausente se reemplaza por $p_e$. Al acotar por uno la capacidad libre y usar $1-x\le e^{-x}$ se obtienen las dos desigualdades de (11).

En la Proposición 10 una hiperarista usa tres recursos: un par requerido y sus dos incidencias cruzadas. Dos recursos determinan a lo sumo un candidato, por lo que el cogrado es a lo sumo uno. La cota de grado $D$ debe cubrir tanto las listas de pares como las incidencias de anfitriones. Bajo las hipótesis de tamaño y grado de la proposición, Ehard–Glock–Joos da un emparejamiento de tamaño al menos $(1-D^{-\epsilon})S/D$. Cada hiperarista elegida asigna un par distinto sin repetir aristas cruzadas. Restamos su tamaño de $|J|$ y multiplicamos por dos como en (1).
