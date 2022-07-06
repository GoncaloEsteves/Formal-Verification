#include <string>
#include <stdio.h>
#include <stdlib.h>
#include <iostream>
#include <fstream>

using namespace std;

int main (int argc, char* argv[]){

    if(argc != 2){
        cout << "<program> #SUDOKU_SIZE\n";
        return 1;
    }

    int N = atoi(argv[1]);
    int N2 = N * N;
    int x[N2][N2][N2];

    ofstream file;
    string filename = "sudoku" + to_string(N) + ".cnf";
    file.open(filename);

    int l, c, n, n2;
    int aux = 1;
    string cond1 = "";
    string cond2 = "";

    for(l = 0; l < N2; l++){
        cond1.append("c   ");

        for(c = 0; c < N2; c++){
            for(n = 0; n < N2; n++)
                x[l][c][n] = aux++;
            
            cond1.append(" " + to_string(x[l][c][0]) + ".." + to_string(x[l][c][N2-1]));
        }

        cond1.append("\n");
    }

    file << "c Sudoku de tamanho " + to_string(N) + "\n\nc  Variáveis e a posição a que estão associadas:\n\n" + cond1;

    aux = (N2*N2) * ((3 * (1 + ((N2*(N2-1))/2))) + 1 + (N2*(N2-1-(2*(N-1)))));
    file << "\np cnf " + to_string(N2*N2*N2) + " " + to_string(aux) + "\n";

    cond1 = "";

    for(l = 0; l < N2; l++){
        for(c = 0; c < N2; c++){
            for(n = 0; n < N2; n++){
                cond1.append(to_string(x[l][c][n]) + " ");

                for(n2 = n+1; n2 < N2; n2++)
                    cond2.append("-" + to_string(x[l][c][n]) + " -" + to_string(x[l][c][n2]) + " 0\n");
            }

            cond1.append("0\n");
        }
    }

    file << "\nc Cada posição da matriz deverá ter um número atribuído\n" + cond1;
    file << "\nc Cada posição da matriz deverá ter no máximo um número atribuído\n" + cond2;

    cond1 = "";
    cond2 = "";

    for(l = 0; l < N2; l++){
        for(n = 0; n < N2; n++){
            for(c = 0; c < N2; c++){
                cond1.append(to_string(x[l][c][n]) + " ");

                for(n2 = c+1; n2 < N2; n2++)
                    cond2.append("-" + to_string(x[l][c][n]) + " -" + to_string(x[l][n2][n]) + " 0\n");
            }

            cond1.append("0\n");
        }
    }

    file << "\nc Cada linha da matriz tem de conter todos os números\n" + cond1;
    file << "\nc Não podem haver números repetidos numa linha\n" + cond2;

    cond1 = "";
    cond2 = "";

    for(c = 0; c < N2; c++){
        for(n = 0; n < N2; n++){
            for(l = 0; l < N2; l++){
                cond1.append(to_string(x[l][c][n]) + " ");

                for(n2 = l+1; n2 < N2; n2++)
                    cond2.append("-" + to_string(x[l][c][n]) + " -" + to_string(x[n2][c][n]) + " 0\n");
            }

            cond1.append("0\n");
        }
    }

    file << "\nc Cada coluna da matriz tem de conter todos os números\n" + cond1;
    file << "\nc Não podem haver números repetidos numa coluna\n" + cond2;

    cond1 = "";
    cond2 = "";

    //Estao a ser inseridas duas "copias" de cada restricao
    for(l = 0; l < N2; l+=N){
        for(c = 0; c < N2; c+=N){
            for(n = 0; n < N2; n++){
                for(int l2 = l; l2 < l+N; l2++){
                    for(int c2 = c; c2 < c+N; c2++){
                        cond1.append(to_string(x[l2][c2][n]) + " ");
                        
                        for(int l3 = l; l3 < l+N; l3++){
                            for(int c3 = c; c3 < c+N; c3++){
                                if(!(l2==l3 || c2==c3))
                                    cond2.append("-" + to_string(x[l2][c2][n]) + " -" + to_string(x[l3][c3][n]) + " 0\n");
                            }
                        }
                    }
                }
                
                cond1.append("0\n");
            }
        }
    }

    file << "\nc Cada submatriz tem de conter todos os números\n" + cond1;
    file << "\nc Não podem haver números repetidos numa submatriz\n" + cond2;

    return 0;
}