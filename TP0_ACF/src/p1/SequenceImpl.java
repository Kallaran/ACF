package p1;

import java.util.Arrays;
import java.util.List;
import java.util.ArrayList;

import test0.Sequence;

public class SequenceImpl implements Sequence{



/**
 * @param l1
 * @param l2
 * @return true if list t1 is a sublist of list t2, where at most one element of t1 may not occur in t2
 */

	public boolean subSeq(Object[] t1, Object[] t2) {	
			
		int pos = -1;
		boolean jokerUsed = false;

		for(int i = 0; i < t1.length; i++) {
			
			//si l'�l�ment de t1 est pr�sent dans t2, on cherche dans la suite de t2 l'�l�ment suivant de t1
			if(presentSuite(t1[i], t2, pos)) {
				
				if(!jokerUsed && resteSuitePresent(t1, t2, i+1, pos)) {//cas o� on zappe potentiellement la suite alors qu'elle est inclue avant 'pos' dans t2
					return true;
				}
				
				pos = positionSuite(t1[i], t2, pos);

			}
			else if(!jokerUsed) {				
				jokerUsed = true;
			}
			else {
				return false;
			}
			
		}
		return true;
		
	}
	
	
//permet de savoir si les �l�ments de 't1' � partir de 'posts1' sont inclus dans 't2' � partir de 'post2'
	private boolean resteSuitePresent(Object[] t1, Object[] t2, int post1, int post2) {
		int pos = post2;
		for(int i = post1; i < t1.length; i++) {
			//si l'�l�ment de t1 est pr�sent dans t2, on cherche dans la suite de t2 l'�l�ment suivant de t1
			if(presentSuite(t1[i], t2, pos)) {
				pos = positionSuite(t1[i], t2, pos);
			}
			else {
				return false;
			}
			
		}
		
		return true;
	}
	

	//fonction qui permet de savoir si l'Object 'o' est present dans le tableau 't' � partir de la position 'pos'
	private boolean presentSuite(Object o, Object[] t, int pos) {
		
		for(int i = pos + 1; i < t.length; i++) {
			if(t[i] == o) {
				return true;
			}
		}
		return false;
	}
	
	
	//on admet que o se trouve dans t
	//rend la position de 'o' dans 't'
	private int positionSuite(Object o, Object[] t, int pos) {
	
		for(int i = pos + 1; i < t.length; i++) {
			if(t[i] == o) {
				return i;
			}
		}
		return 300; //on n'est pas cens� arriver ici		
	}




	

}

