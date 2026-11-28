import Sagitta.Map.BuenaFundacion
import Sagitta.Map.Contador
import Sagitta.Map.DescensoOrdinal
import Sagitta.Map.PLS
import Sagitta.Map.BusquedaNP
import Sagitta.Map.DescensoCreciente
import Sagitta.Map.DescensoAcotado
import Sagitta.Map.AlgoritmoEstandar
import Sagitta.Map.ExhaustivoTiempo
import Sagitta.Map.Vara
import Sagitta.Map.PLSConcreto
import Sagitta.Map.CuantoTarda
import Sagitta.Map.OtraDireccion
import Sagitta.Map.Goodstein
import Sagitta.Map.Circuitos
import Sagitta.Map.Acotada
import Sagitta.Map.Definibles
import Sagitta.Map.SigmaNP
import Sagitta.Map.Teoria
import Sagitta.Map.T12
import Sagitta.Map.Secuentes
import Sagitta.Map.Shannon
import Sagitta.Map.FormaDelTiempo
import Sagitta.Map.Landau
import Sagitta.Map.Jerarquia
import Sagitta.Map.Decidir
import Sagitta.Map.Consumo
import Sagitta.Map.ConsumoNP
import Sagitta.Map.ConsumoOmega
import Sagitta.Map.Savitch
import Sagitta.Map.Alternancia
import Sagitta.Map.Cuasipolinomial
import Sagitta.Map.CorteRacional
import Sagitta.Map.Finitud
import Sagitta.Map.Infinito
import Sagitta.Map.Relleno
import Sagitta.Map.LargoInfinitoS12
import Sagitta.Map.KPT
import Sagitta.Map.TiempoCobham
import Sagitta.Map.DeltaUno
import Sagitta.Map.CookS12
import Sagitta.Map.Parikh
import Sagitta.Map.Arranque
import Sagitta.Map.Arranque2
import Sagitta.Map.DefinibleCobham
import Sagitta.Map.Borde.RellenoExponencial

/-!
# De qué axiomas depende cada cosa

`lake build` imprime la lista. Lo que se ve: los enunciados (`PIgualNP`, `TeoremaGoodstein`) y los
teoremas arrastran los tres axiomas de Lean porque Mathlib los usa por dentro (polinomios, mínimos,
conjuntos), no porque el contenido los necesite.
-/

open Sagitta.Map

#print axioms P
#print axioms NP
#print axioms PIgualNP
#print axioms pIgualNP_iff_verificarImplicaResolver
#print axioms sinDescensoInfinito_nat
#print axioms Descenso.existe_optimo
#print axioms goodstein
#print axioms TeoremaGoodstein
#print axioms goodstein_tres
#print axioms tamMin
#print axioms existe_funcion_exponencial
#print axioms existe_problema_exponencial
#print axioms mul_pow_lt_dos_pow
#print axioms existe_problema_fuera_de_PsobrePoly
#print axioms pDistintoNP_of_sinCircuitos
#print axioms Acotada.nat_esModeloBASIC
#print axioms Acotada.nat_esModeloS12
#print axioms Acotada.teoremaDeBuss_iff
#print axioms Acotada.definible_id
#print axioms Acotada.demuestraTotalSinCota_de_cota
#print axioms Acotada.buss_vale_en_id
#print axioms Acotada.numeroDe_inyectiva
#print axioms Acotada.piIgualCoNP_de_sigma
#print axioms Acotada.npDistintoCoNP_iff
#print axioms Acotada.modelo_basic_iff
#print axioms Acotada.realize_pindAx
#print axioms Acotada.modelo_S12_iff
#print axioms Acotada.demuestra_iff_models
#print axioms Acotada.demuestra_iff_finito
#print axioms Acotada.nat_esModeloT12
#print axioms Acotada.t02_de_t12
#print axioms Acotada.modelo_T12_iff
#print axioms Acotada.demuestraT12_iff_models
#print axioms Acotada.demuestraT12_iff_finito
#print axioms Acotada.Deriva.correcta
#print axioms Acotada.Deriva.verdadera
#print axioms Acotada.EsSigma1.subst
#print axioms Acotada.Deriva.sigma1_de_ancl
#print axioms Acotada.Deriva.formulasDeCorte_sigma1
#print axioms Acotada.Deriva.sinCortesLibres_de_sinCortes
#print axioms Descenso.desciende_desde
#print axioms Contador.pasos_exactos
#print axioms Contador.descenso_largo
#print axioms Contador.optimo_unico
#print axioms Contador.atajo_correcto
#print axioms DescensoEn.termina
#print axioms Recarga.pasos_exactos
#print axioms Recarga.sin_cota
#print axioms DescensoEn.a_naturales
#print axioms Recarga.colapsa
#print axioms ProblemaPLS.desciende
#print axioms ProblemaPLS.existe_solucion
#print axioms Componer.esPolinomial_comp
#print axioms Basicas.esPolinomial_y
#print axioms Basicas.esPolinomial_fst
#print axioms Comparar.mayor_encodeNat
#print axioms Comparar.esPolinomial_le
#print axioms Basicas.esPolinomial_no
#print axioms Pares.esPolinomial_dup
#print axioms Pares.esPolinomial_swap
#print axioms Primero.esPolinomial_primero
#print axioms Primero.esPolinomial_pares
#print axioms cierrePolinomial
#print axioms pls_sub_tfnp
#print axioms Exhaustiva.ruta
#print axioms Exhaustiva.ultimo_esOptimo
#print axioms np_y_conp_de_tfnp
#print axioms np_sub_conp_de_tfnp
#print axioms ProblemaPLS.destino_esSolucion
#print axioms hay_certificado_iff
#print axioms np_por_destino
#print axioms ExhaustivoTiempo.encodeNat_costo
#print axioms ExhaustivoTiempo.esPolinomial_vacia
#print axioms ExhaustivoTiempo.esPolinomial_sig
#print axioms ExhaustivoTiempo.esPolinomial_menor
#print axioms ExhaustivoTiempo.esPolinomial_si
#print axioms ExhaustivoTiempo.esPolinomial_costo
#print axioms ExhaustivoTiempo.exhaustivo_polinomial
#print axioms ExhaustivoTiempo.np_por_destino_polinomial
#print axioms Vara.esPolinomial_concat
#print axioms Vara.esPolinomial_mult
#print axioms Vara.tieneVara
#print axioms Vara.np_al_algoritmo_estandar
#print axioms PLSConcreto.existe_problemaPLS
#print axioms PLSConcreto.solucion_trivial
#print axioms PLSConcreto.np_por_pls
#print axioms CuantoTarda.pasos_exponencial
#print axioms CuantoTarda.pasos_sin_certificado
#print axioms MientrasMaquina.esPolinomial_mientras
#print axioms Bloques.esPolinomial_leeTotal
#print axioms BusquedaPrefijos.destinoBusqueda_eq
#print axioms PreguntaNP.lenguaje_en_NP
#print axioms OtraDireccion.destino_polinomial
#print axioms OtraDireccion.destino_polinomial_de_pIgualNP
#print axioms OtraDireccion.verificarImplicaResolver_iff
#print axioms Creciente.termina
#print axioms Creciente.largo
#print axioms Creciente.llega
#print axioms Creciente.no_colapsa
#print axioms Acotado.colapsa_por_conteo
#print axioms Acotado.BusquedaOmega2.a_naturales
#print axioms Shannon.shannon
#print axioms Shannon.diez_bits_setenta_compuertas
#print axioms Shannon.shannon_hasta
#print axioms Shannon.diez_bits_hasta_setenta_compuertas
#print axioms Shannon.shannon_asintotico
#print axioms Shannon.calcula_combinar
#print axioms Shannon.toda_funcion_calculable
#print axioms tamMin_lt_top
#print axioms sucesion_lt_top
#print axioms Tiempo.frente_eq_iterate
#print axioms Tiempo.frente_determinista
#print axioms Tiempo.corrida_determinista
#print axioms Tiempo.isCompact_corrida
#print axioms Tiempo.isOpen_alguna_vez
#print axioms Tiempo.isClosed_siempre
#print axioms Tiempo.konig
#print axioms Tiempo.angelica_iff
#print axioms Tiempo.demoniaca_acotada
#print axioms Tiempo.llega_por_mitades
#print axioms Tiempo.llega_de_uno_en_uno
#print axioms Tiempo.pol_mul
#print axioms Tiempo.pol_mul_n
#print axioms Tiempo.pol_comp
#print axioms Tiempo.pol_iterate
#print axioms Tiempo.costo_iterado_aditivo
#print axioms Tiempo.pol_menor_dos_pow
#print axioms Tiempo.iterada_doblar_escapa
#print axioms Tiempo.iterada_doblar_no_pol_por_pol
#print axioms Tiempo.iterada_doblar_en_exp
#print axioms Tiempo.iterada_cuadrar_no_exp
#print axioms Tiempo.ncard_frente_binario
#print axioms Tiempo.frente_binario_escapa
#print axioms Tiempo.F_eq_fastGrowing_two
#print axioms Tiempo.F_strictMono
#print axioms Tiempo.capa_comp
#print axioms Tiempo.capa_iterate
#print axioms Tiempo.F_succ_no_capa
#print axioms Tiempo.capa_estricta
#print axioms Tiempo.pol_sub_capa_dos
#print axioms Tiempo.cuadrar_no_capa_uno
#print axioms Tiempo.Fω_no_capa
#print axioms Tiempo.capaE_mono
#print axioms Tiempo.Fω_no_capaE_top
#print axioms Tiempo.isOpen_capa_finita
#print axioms Tiempo.no_isOpen_top
#print axioms Tiempo.tiende_a_omega
#print axioms Tiempo.adversario
#print axioms Tiempo.costo_adversario
#print axioms Tiempo.barrer_alcanza
#print axioms Tiempo.te_dicen
#print axioms Tiempo.decidir_ramas
#print axioms Tiempo.decidir_ramas_escapa
#print axioms Tiempo.rala_escapa
#print axioms Tiempo.rala_certificado
#print axioms Tiempo.dos_pow_pol_iff
#print axioms Cobham.definible_es_cobham
#print axioms Cobham.definibleEsPolinomial
#print axioms DeltaUno.esPolinomial_numeroDe
#print axioms DeltaUno.esPolinomial_esCero
#print axioms DeltaUno.decide_cobham
#print axioms DeltaUno.deltaUno_en_P
#print axioms DeltaUno.np_sub_p_si_s12_decide
#print axioms CookS12.np_a_cslib
#print axioms CookS12.mem_P_de_bits
#print axioms CookS12.np_sub_p_de_dificil
#print axioms CookS12.np_sub_p_de_sat
#print axioms CookS12.np_sub_p_si_s12_decide_sat
#print axioms CookS12.pIgualNP_si_s12_decide_sat
#print axioms Acotada.Parikh.segmento_S12
#print axioms Acotada.Parikh.existe_c_sin_cota
#print axioms Acotada.Parikh.parikh_de_monotonas
#print axioms Acotada.Parikh.monotonas
#print axioms Acotada.Parikh.parikh
#print axioms DeltaUno.definible_sin_cota_es_polinomial
#print axioms Acotada.Arranque.size_suma
#print axioms Acotada.Arranque.size_prod
#print axioms Acotada.Arranque.size_smash
#print axioms Acotada.Arranque.largo_termino
#print axioms Acotada.Arranque.lind
#print axioms Acotada.Arranque.EsSigma1.relabel
#print axioms Acotada.Arranque.EsPi1.relabel
#print axioms Acotada.Arranque.pind_pi
#print axioms Acotada.Arranque.s12ContieneT02
#print axioms Acotada.Arranque.smash_uno_uno
#print axioms Acotada.Arranque.smash_uno_mitad
#print axioms Acotada.Arranque.bits_altos_unico
#print axioms Acotada.Arranque.pind_pi_t12
#print axioms Acotada.Arranque.lt_smash_uno
#print axioms Acotada.Arranque.bits_altos_t12
#print axioms Acotada.Arranque.pind_t12
#print axioms Acotada.Arranque.t12ContieneS12
#print axioms Acotada.DefinibleCobham.termino_definible
#print axioms Acotada.DefinibleCobham.cond_definible
#print axioms Acotada.DefinibleCobham.lt_smash_uno_s12
#print axioms Acotada.DefinibleCobham.resta_existe
#print axioms Acotada.DefinibleCobham.resta_definible
#print axioms Acotada.DefinibleCobham.comp_definible
#print axioms Acotada.DefinibleCobham.sinRn_definible
#print axioms Acotada.DefinibleCobham.cob_definible
#print axioms Acotada.DefinibleCobham.definible_pred
#print axioms Acotada.DefinibleCobham.polinomialEsDefinible_de
#print axioms Acotada.DefinibleCobham.teoremaDeBuss_de
#print axioms Consumo.Arbol.costo_idempotente
#print axioms Consumo.Arbol.costo_aditivo
#print axioms Consumo.Arbol.tiempo_completo_escapa
#print axioms Consumo.Arbol.tiempo_lt_dos_pow_espacio
#print axioms Consumo.Arbol.existe_rama_espacio
#print axioms Consumo.consumido_iff_continuo
#print axioms Consumo.pila_no_continua
#print axioms Consumo.medida_omega
#print axioms Consumo.nodos_piezas
#print axioms Consumo.kraft
#print axioms Consumo.cortes_cubren
#print axioms Consumo.piezas_de_masa_acotada
#print axioms Consumo.palomar_piezas
#print axioms Consumo.medida_cil
#print axioms Consumo.suma_cortes_omega
#print axioms Consumo.corte_uniforme
#print axioms Consumo.nu_omega_le
#print axioms Tiempo.alcanza_corto
#print axioms Tiempo.alc_iff
#print axioms Tiempo.savitch
#print axioms Tiempo.acepta_iff
#print axioms Tiempo.savitch_bits
#print axioms Tiempo.savitch_menor_que_frente
#print axioms Tiempo.Juego.hojas_le_dos_pow_prof
#print axioms Tiempo.Juego.prof_jugarArbol
#print axioms Tiempo.valor_juegoSav
#print axioms Tiempo.prof_juegoSav
#print axioms Tiempo.hojas_juegoSav
#print axioms Tiempo.savitch_alternante
#print axioms Cobham.kpt
#print axioms Cobham.demuestraAEA_de_gana
#print axioms Cobham.kpt_iff
#print axioms Cobham.kpt_abierta
#print axioms Tiempo.cuasi_no_pol
#print axioms Tiempo.cuasi_en_exp
#print axioms Tiempo.cuasi_no_O_succ
#print axioms Tiempo.cuasi_en_bits
#print axioms Tiempo.elecciones_no_pol
#print axioms Tiempo.savitch_cuasi
#print axioms Tiempo.CorteRacional.descripcion_no_acotada
#print axioms Tiempo.CorteRacional.existe_irracional
#print axioms Tiempo.CorteRacional.certificados_no_acotados
#print axioms Tiempo.CorteRacional.levin_en_O
#print axioms Tiempo.CorteRacional.constantes_no_acotadas
#print axioms Tiempo.Finitud.tamMin_alcanzado
#print axioms Tiempo.Finitud.limite_finito_iff
#print axioms Tiempo.Finitud.no_llega
#print axioms Tiempo.Finitud.escalera_cuasi_no_llega
#print axioms Tiempo.Finitud.psobrePoly_iff_grado
#print axioms Tiempo.Finitud.existe_grado_infinito
#print axioms Tiempo.Infinito.io_iff_largo_infinito
#print axioms Tiempo.Infinito.circuito_en_el_infinito
#print axioms Tiempo.Infinito.psobrePoly_iff_infinito
#print axioms Tiempo.Infinito.fuera_iff_largo_infinito
#print axioms Tiempo.Infinito.ambos_a_la_vez
#print axioms Tiempo.Infinito.existe_solo_en_el_limite
#print axioms Acotada.LargoS12.segmento_inicial
#print axioms Acotada.LargoS12.mayor_que_todo_numeral
#print axioms Acotada.LargoS12.no_deriva_iff_contraejemplo
#print axioms Acotada.LargoS12.contraejemplo_no_estandar
#print axioms Acotada.LargoS12.largo_infinito_s12
#print axioms Acotada.LargoS12.largo_infinito_s12_de_verdad
#print axioms Acotada.LargoS12.cota_falsa_en_uno
#print axioms Acotada.LargoS12.cotaInferiorSAT_vacia
#print axioms Acotada.LargoS12.cota_inferior_largo_infinito
#print axioms Acotada.LargoS12.ultrapoder_esModeloS12
#print axioms Acotada.LargoS12.ultrapoder_honesto
#print axioms Acotada.LargoS12.ultrapoder_no_estandar
#print axioms Acotada.LargoS12.contraste
#print axioms Tiempo.Relleno.tamMin_fijar
#print axioms Tiempo.Relleno.psobrePoly_de_denso
#print axioms Tiempo.Relleno.psobrePoly_iff_denso
#print axioms Tiempo.Relleno.fuera_iff_huecos
#print axioms Tiempo.Relleno.fuera_iff_huecos_infinitos
#print axioms Tiempo.Relleno.no_rellenable_soloEnElLimite
#print axioms Tiempo.Relleno.rellenable_satMarco
#print axioms Tiempo.Relleno.satBits_de_satMarco
#print axioms Tiempo.Relleno.satBits_de_denso
#print axioms Tiempo.Relleno.huecos_de_sat
#print axioms Tiempo.Relleno.huecos_de_sat_infinito
#print axioms Tiempo.Relleno.control_densidad
#print axioms Tiempo.Relleno.control_en_el_infinito
#print axioms Acotada.LargoS12.expresa_solo_pide_verdad
#print axioms Acotada.LargoS12.desde_chico_vacia
#print axioms Borde.RellenoExponencial.diagonalRellena_mem_P
#print axioms Borde.RellenoExponencial.computableInO_decisor
#print axioms Borde.RellenoExponencial.existe_dificil_con_relleno_facil
#print axioms Borde.RellenoExponencial.decisor_rellenar
#print axioms Borde.RellenoExponencial.no_reduce_a_relleno_expo
#print axioms Borde.RellenoExponencial.primeraLey_de_polinomial
#print axioms Borde.RellenoExponencial.no_primeraLey_expo
#print axioms Borde.RellenoExponencial.expo_no_polinomial
