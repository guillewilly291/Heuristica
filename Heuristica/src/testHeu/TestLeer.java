package testHeu;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Scanner;
import org.jacop.core.*;
import org.jacop.jasat.utils.structures.IntVec;
import org.jacop.satwrapper.SatWrapper;
import org.jacop.constraints.*; 
import org.jacop.search.*; 



/*public class TestLeer {

	public static int numLineas(String archivo) throws FileNotFoundException {
		File input = new File(archivo);
		Scanner iterate = new Scanner(input);
		int numLines = 0;
		while (iterate.hasNextLine()) {
			String currLine = iterate.nextLine();
			numLines++;
		}
		return numLines;
	}
		public static char[][] leerArchivo(String archivo) throws FileNotFoundException, IOException {
		int numLineas= numLineas(archivo);
		String cadena;
		FileReader f = new FileReader(archivo);

		BufferedReader b = new BufferedReader(f);
		String size = b.readLine();
		char mapa[][] = new char[numLineas][size.length()];
		int i = 1;
		cadena = size;
		for (int j = 0; j < size.length(); j++) {
			mapa[0][j] = cadena.substring(j, j + 1);
		}

		while ((cadena = b.readLine()) != null) {
			for (int j = 0; j < cadena.length(); j++) {
				mapa[i][j] = cadena.substring(j, j + 1);
			}
			i++;
		}
		b.close();

		for (int z = 0; z < size.length(); z++) {
			for (int y = 0; y < size.length(); y++) {
				System.out.print(mapa[z][y] + " ");

			}
			System.out.println();
		}
		
		return ; 
	}
 CODIGO ANTIGUO, INTRODUZCO EL DE LEERARCHIVO DEL FICHJERTO SATal DE ESTOS PARA IR PROBANDO PORQUE ESTE HAY QUE MODIFICARLO 
	public static void main(String[] args) throws IOException {
		//muestraContenido("C:/Users/GuillermoDeLeceaRamo/Desktop/test4.txt");
	}
	
	
	/*Codigo del ejemplo de seguridad que servira como base para sentar las clausulas*/

public class TestLeer {

	

	public static void main(String args[]) throws IOException{
			File fichero = new File("C:/Users/Sergio/Desktop/mapa1.txt"); 
			int numeroSerpientes = Integer.parseInt("3");
			char[][] mapa = leerFichero(fichero.getPath());
			char[][] mapaSol = mapa;
			int numeroFilas = mapa.length;
			int numeroColumnas = mapa[0].length;
			Store store = new Store();
			SatWrapper satWrapper = new SatWrapper(); 
			store.impose(satWrapper);					/* Importante: sat problem */


			/* Creamos las variables binarias */
			
			BooleanVar[][] al = new BooleanVar[numeroFilas][numeroColumnas];	//Al en cada una de las casillas del mapa¿?
			
			for(int i= 0 ; i < numeroFilas;i++){
				for(int j= 0 ; j < numeroColumnas;j ++){	
					al[i][j] = new BooleanVar(store, "Al esta en la casilla " + i + " " + j);	
					satWrapper.register(al[i][j]);		
				}			
			}	
			
			
			BooleanVar[][][] serpiente = new BooleanVar[numeroSerpientes][numeroFilas][numeroColumnas];	//Al en cada una de las casillas del mapa¿?
		for(int x=0; x < numeroSerpientes; x++ ){		
			for(int i = 0 ; i < numeroFilas;i++){
				for(int j= 0 ; j < numeroColumnas;j ++){	
					serpiente[x][i][j] = new BooleanVar(store, "La serpiente " + x + " esta en la posicion " + i + " " + j);
					satWrapper.register(serpiente[x][i][j]);		
				}			
			}
		}	
			/* Obtenemos los literales no negados de las variables */
		
	
			int alLiteral[][]= new int [numeroFilas][numeroColumnas]; 
			int serLiteral[][][]= new int [numeroSerpientes][numeroFilas][numeroColumnas]; 
			
			
			int numeroTotalVariables = numeroFilas * numeroColumnas + numeroSerpientes*(numeroFilas * numeroColumnas);
			
			BooleanVar[] allVariables = new BooleanVar[numeroTotalVariables];
			
			int posicionAllVariables = 0;
			
			for(int i = 0; i < numeroFilas; i++) {
				for (int j = 0; j < numeroColumnas; j++) {
						alLiteral[i][j] = satWrapper.cpVarToBoolVar(al[i][j], 1, true);
						allVariables[posicionAllVariables] = al[i][j];
						posicionAllVariables++;
					}
			}
			
			for(int x = 0; x < numeroSerpientes; x++) {
				for (int i = 0; i < numeroFilas; i++) {
					for (int j = 0; j < numeroColumnas; j++) {
							serLiteral[x][i][j] = satWrapper.cpVarToBoolVar(serpiente[x][i][j], 1, true);
							allVariables[posicionAllVariables] = serpiente[x][i][j];
							posicionAllVariables++;
						}
				}
			}
			
			/* El problema se va a definir en forma CNF, por lo tanto, tenemos
			   que añadir una a una todas las clausulas del problema */
			
			/* Clausula para restringir que al y los fantasmas solo pueden estar en celdas vacias.
			 * Para ello recorremos la matriz y si hay una pared o capsula negamos dicho literal  */
			
			for(int x = 0;x < numeroFilas;x++){
				for(int y = 0;y < numeroColumnas;y++){
					if(mapa[x][y] == '%' || mapa[x][y] == 'O' || mapa[x][y] == 'E' || mapa[x][y] == 'K'){
						IntVec clause = new IntVec(satWrapper.pool);
						clause.add(-alLiteral[x][y]);
						satWrapper.addModelClause(clause.toArray());
						for(int z = 0;z < numeroSerpientes;z++){
							IntVec clause1 = new IntVec(satWrapper.pool);
							clause1.add(-serLiteral[z][x][y]);
							satWrapper.addModelClause(clause1.toArray());
						}
					}
				}
			}
			
			/* Clausula para que no haya fantasmas en la misma fila ni en la misma posicion
			 * Añadimos las clausulas para que no haya fantasmas en la misma fila ni
			 * en la misma posicion
			 */

			
			for(int x = 0;x < numeroFilas;x++){
				for(int y =0;y < numeroSerpientes;y++){
					for(int z = 0;z < numeroColumnas;z++){
						for(int a = 0;a < numeroSerpientes;a++){
							for(int b = 0;b < numeroColumnas;b++){
								if(y != a || z != b){ /*No podemos añadir si son el mismo fantasma y estan en la misma columna(estarian en la misma posicion)*/
									addClause(satWrapper, -serLiteral[y][x][z], -serLiteral[a][x][b]);
								}
							}
						}
					}
				}
			}
			

			/* Clausula para que cada fantasma solo se pueda colocar una vez(limite superior)*/
			for(int x = 0;x < numeroSerpientes;x++){
				for(int y =0;y < numeroFilas;y++){
					for(int z = 0;z < numeroColumnas;z++){
						for(int a = 0;a < numeroFilas;a++){
							for(int b = 0;b < numeroColumnas;b++){
								if(y != a || z != b){/*No se pueden añadir la clausula si estan la misma posicion  */
									addClause(satWrapper, -serLiteral[x][y][z], -serLiteral[x][a][b]);
								}
							}
						}
					}
				}
			}
			/* Clausula para que cada fantasma se tenga que colocar una vez(limite inferior)*/
			for(int x = 0;x < numeroSerpientes;x++){
				IntVec clause = new IntVec(satWrapper.pool);
				for(int y =0;y < numeroFilas;y++){
					for(int z = 0;z < numeroColumnas;z++){
						clause.add(serLiteral[x][y][z]);
					}
				}
				satWrapper.addModelClause(clause.toArray());
			}
	
			
			for (int i = 0; i < numeroFilas; i++) {
				for (int j = 0; j < numeroColumnas; j++) {
					for (int a = 0; a < numeroSerpientes; a++) {
						for (int x = 0; x < numeroColumnas; x++) {						
							addClause(satWrapper, -alLiteral[i][j], -serLiteral[a][i][j]); /*No pueden estar en la misma posicion*/
							addClause(satWrapper, -alLiteral[i][j], -serLiteral[a][i][x]); /*No pueden estar en la misma posicion*/		
						}
					}
				}
			}	
			
			/* Clausula para que solo se pueda colocar un al (limite superior)*/
			for(int x = 0;x < numeroFilas;x++){
				for(int y = 0;y < numeroColumnas;y++){
					for(int a = 0;a < numeroFilas;a++){
						for(int b = 0;b < numeroColumnas;b++){
							if(x != a || y != b){ /*No podemos añadir si estan en la misma posicion*/
								addClause(satWrapper,-alLiteral[x][y], -alLiteral[a][b]);
							}
						}
					}
				}
			}
			
			/* Clausula para que se tenga que colocar un al(limite inferior)*/
			IntVec clause = new IntVec(satWrapper.pool);
			for(int x = 0;x < numeroFilas;x++){
				for(int y = 0;y < numeroColumnas;y++){
					clause.add(alLiteral[x][y]);
				}
			}	
			satWrapper.addModelClause(clause.toArray());
			
			
			
			
			
			/* Resolvemos el problema */
			Search<BooleanVar> search = new DepthFirstSearch<BooleanVar>();
			SelectChoicePoint<BooleanVar> select = new SimpleSelect<BooleanVar>(allVariables,
					new SmallestDomain<BooleanVar>(), new IndomainMin<BooleanVar>());
			Boolean result = search.labeling(store, select);

			if (result) {
				File laberintofinal = null;
				PrintWriter writer = null;
				try {
					/* Creacion y apertura del fichero, y creacion de BufferedWriter para poder hacer una escritura */
					laberintofinal = new File(fichero+".output");
					writer = new PrintWriter (laberintofinal, "utf-8");
					/*Introducimos en la matriz laberinto el al*/
					for(int x = 0;x < numeroFilas;x++){
						for(int y = 0;y < numeroColumnas;y++){
							if(al[x][y].dom().value() == 1){
								mapaSol[x][y] = 'A';
							}
						}
					}
					/*Introducimos en la matriz laberinto los fantasmas */
					for(int x = 0;x < numeroSerpientes;x++){
						for(int y = 0;y < numeroFilas;y++){
							for(int z = 0;z < numeroColumnas;z++){
								if(serpiente[x][y][z].dom().value() == 1){
									mapaSol [y][z] = 'S';
								}
							}
						}
					}
					/*Escribimos la matriz en el fichero que hemos creado*/
					int x;
					int y;
					for(x = 0;x < numeroFilas;x++){
						for(y = 0;y < numeroColumnas;y++){
							writer.append(mapaSol[x][y]);
						}
						writer.println();
					}					
				} catch(Exception e){
				         e.printStackTrace();
				} finally {
			         /* En el finally cerramos el fichero, para asegurarnos
			         * que se cierra tanto si todo va bien como si salta 
			          una excepcion.*/
			         try{                    
			            if( null != writer ){   
			               writer.close();     
			            }                  
			         }catch (Exception e2){ 
			            e2.printStackTrace();
			         }
			      }
				System.out.println("Solution: ");
				for (int i = 0; i < numeroFilas; i++) {
					for (int j = 0; j < numeroColumnas; j++) {
						if (al[i][j].dom().value() == 1)
							System.out.println(al[i][j].id());
						mapaSol[i][j] = 'A';
					}
				}

				for (int i = 0; i < numeroSerpientes; i++) {
					for (int j = 0; j < numeroFilas; j++) {
						for (int k = 0; k < numeroColumnas; k++) {
							if (serpiente[i][j][k].dom().value() == 1)
								System.out.println(serpiente[i][j][k].id());
							mapaSol[j][k] = 'S';
						}
					}
				}

			} else {
				System.out.println("El problema es insatisfacible");
			}
			
			
		}		
			
		public static void addClause(SatWrapper satWrapper, int literal1, int literal2){
			IntVec clause = new IntVec(satWrapper.pool);
			clause.add(literal1);
			clause.add(literal2);
			satWrapper.addModelClause(clause.toArray());
		}


		public static void addClause(SatWrapper satWrapper, int literal1, int literal2, int literal3){
			IntVec clause = new IntVec(satWrapper.pool);
			clause.add(literal1);
			clause.add(literal2);
			clause.add(literal3);
			satWrapper.addModelClause(clause.toArray());
		}
		
		
		
		public static char[][] leerFichero(String archivo) throws FileNotFoundException, IOException {
			String cadena;
			try {
				FileReader f = new FileReader(archivo);
				BufferedReader b = new BufferedReader(f);
				FileReader d = new FileReader(archivo);
				BufferedReader r = new BufferedReader(d);
				int filas = 0;
				int columnas = 0;
				int c = 0;
				int i = 0;
				int j = 0;
				while ((cadena = r.readLine()) != null) {
					filas++;
					c = columnas;
					columnas = cadena.length();
				}
				char[][] lab = new char[filas][c];
				while ((cadena = b.readLine()) != null) {
					j = 0;
					while (j < cadena.length()) {
						lab[i][j] = cadena.charAt(j);
						
						j++;
					}
					
					i++;
				}
				b.close();
				r.close();
				return lab;
			} catch (IOException e) {
				System.out.println("Excepcion leyendo fichero:" + e);
				return null;
			}

		}
	}

	
	
	
	
	
	
	
	
	
