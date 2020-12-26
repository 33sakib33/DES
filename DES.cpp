
// Implementation of DES.
// Nazmus Sakib Ahmed
// BSSE 1108 

#include<bits/stdc++.h>
using namespace std;
#define mod 1000000009
#define cin1(x) cin>>x
#define cin2(x,y) cin>>x>>y
#define cin3(x,y,z) cin>>x>>y>>z
#define ll long long
#define mp make_pair
#define pb push_back
#define nl printf("\n")
#define ff first
#define ss second
#define set0(a) memset ((a), 0 , sizeof(a))
#define set1(a) memset((a),-1,sizeof (a))
#define pi pair<int, int>
#define ps pair<string, string>
#define pl pair<long, long>
#define pll pair<long long, long long>
#define vll vector<long long>
#define vl vector<long>
#define vi vector<int>
#define vs vector<string>
#define vps vector< ps >
#define vpi vector< pi >
#define vpl vector< pl >
#define vpll vector< pll >
#define flash  ios_base::sync_with_stdio(false); cin.tie(NULL);
#define tc(t,T) for(long long t=0;t<T;t++)
#define rep(i,s,n,d) for(long long i=s;i<n;i=i+d)
//A bitset vector to save the subkeys
vector<bitset<48>>keyRound(20);

//These tables and boxes have been from the internet
//Initial permutation table
vi ip  { 58, 50, 42, 34, 26, 18, 10, 2, 
                             60, 52, 44, 36, 28, 20, 12, 4, 
                             62, 54, 46, 38, 30, 22, 14, 6, 
                             64, 56, 48, 40, 32, 24, 16, 8, 
                             57, 49, 41, 33, 25, 17, 9, 1, 
                             59, 51, 43, 35, 27, 19, 11, 3, 
                             61, 53, 45, 37, 29, 21, 13, 5, 
                             63, 55, 47, 39, 31, 23, 15, 7 }; 
 
//Final permuation table                            
vi fp { 40, 8, 48, 16, 56, 24, 64, 32, 
				39, 7, 47, 15, 55, 23, 63, 31, 
				38, 6, 46, 14, 54, 22, 62, 30, 
				37, 5, 45, 13, 53, 21, 61, 29, 
				36, 4, 44, 12, 52, 20, 60, 28, 
				35, 3, 43, 11, 51, 19, 59, 27, 
				34, 2, 42, 10, 50, 18, 58, 26, 
				33, 1, 41, 9, 49, 17, 57, 25 }; 
//expansion D-box
vi exp1 { 31, 0, 1, 2, 3, 4, 3, 4, 5, 6, 7, 8, 7, 8, 9, 10, 11, 12, 11, 12, 13,
                    		14, 15, 16, 15, 16, 17, 18, 19, 20, 19, 20, 21, 22, 23, 24, 23, 24, 
                    		25, 26, 27, 28, 27, 28, 29, 30, 31, 0 };

//The eight S-boxes
int sBox[8][4][16] = { { 14, 4, 13, 1, 2, 15, 11, 8, 3, 10, 6, 12, 5, 9, 0, 7, 
                          0, 15, 7, 4, 14, 2, 13, 1, 10, 6, 12, 11, 9, 5, 3, 8, 
                          4, 1, 14, 8, 13, 6, 2, 11, 15, 12, 9, 7, 3, 10, 5, 0, 
                          15, 12, 8, 2, 4, 9, 1, 7, 5, 11, 3, 14, 10, 0, 6, 13 }, 
                        { 15, 1, 8, 14, 6, 11, 3, 4, 9, 7, 2, 13, 12, 0, 5, 10, 
                          3, 13, 4, 7, 15, 2, 8, 14, 12, 0, 1, 10, 6, 9, 11, 5, 
                          0, 14, 7, 11, 10, 4, 13, 1, 5, 8, 12, 6, 9, 3, 2, 15, 
                          13, 8, 10, 1, 3, 15, 4, 2, 11, 6, 7, 12, 0, 5, 14, 9 }, 
  
                        { 10, 0, 9, 14, 6, 3, 15, 5, 1, 13, 12, 7, 11, 4, 2, 8, 
                          13, 7, 0, 9, 3, 4, 6, 10, 2, 8, 5, 14, 12, 11, 15, 1, 
                          13, 6, 4, 9, 8, 15, 3, 0, 11, 1, 2, 12, 5, 10, 14, 7, 
                          1, 10, 13, 0, 6, 9, 8, 7, 4, 15, 14, 3, 11, 5, 2, 12 }, 
                        { 7, 13, 14, 3, 0, 6, 9, 10, 1, 2, 8, 5, 11, 12, 4, 15, 
                          13, 8, 11, 5, 6, 15, 0, 3, 4, 7, 2, 12, 1, 10, 14, 9, 
                          10, 6, 9, 0, 12, 11, 7, 13, 15, 1, 3, 14, 5, 2, 8, 4, 
                          3, 15, 0, 6, 10, 1, 13, 8, 9, 4, 5, 11, 12, 7, 2, 14 }, 
                        { 2, 12, 4, 1, 7, 10, 11, 6, 8, 5, 3, 15, 13, 0, 14, 9, 
                          14, 11, 2, 12, 4, 7, 13, 1, 5, 0, 15, 10, 3, 9, 8, 6, 
                          4, 2, 1, 11, 10, 13, 7, 8, 15, 9, 12, 5, 6, 3, 0, 14, 
                          11, 8, 12, 7, 1, 14, 2, 13, 6, 15, 0, 9, 10, 4, 5, 3 }, 
                        { 12, 1, 10, 15, 9, 2, 6, 8, 0, 13, 3, 4, 14, 7, 5, 11, 
                          10, 15, 4, 2, 7, 12, 9, 5, 6, 1, 13, 14, 0, 11, 3, 8, 
                          9, 14, 15, 5, 2, 8, 12, 3, 7, 0, 4, 10, 1, 13, 11, 6, 
                          4, 3, 2, 12, 9, 5, 15, 10, 11, 14, 1, 7, 6, 0, 8, 13 }, 
                        { 4, 11, 2, 14, 15, 0, 8, 13, 3, 12, 9, 7, 5, 10, 6, 1, 
                          13, 0, 11, 7, 4, 9, 1, 10, 14, 3, 5, 12, 2, 15, 8, 6, 
                          1, 4, 11, 13, 12, 3, 7, 14, 10, 15, 6, 8, 0, 5, 9, 2, 
                          6, 11, 13, 8, 1, 4, 10, 7, 9, 5, 0, 15, 14, 2, 3, 12 }, 
                        { 13, 2, 8, 4, 6, 15, 11, 1, 10, 9, 3, 14, 5, 0, 12, 7, 
                          1, 15, 13, 8, 10, 3, 7, 4, 12, 5, 6, 11, 0, 14, 9, 2, 
                          7, 11, 4, 1, 9, 12, 14, 2, 0, 6, 10, 13, 15, 3, 5, 8, 
                          2, 1, 14, 7, 4, 10, 8, 13, 15, 12, 9, 0, 3, 5, 6, 11 } }; 

//Permutation choice-1 box for the left part of the key
vi pc1L{ 56, 48, 40, 32, 24, 16, 8, 0, 57, 49, 41, 33, 25, 17, 9, 1, 58, 50, 42, 34, 26, 18, 10, 2, 59, 51, 43, 35 };

//Permuation choice -1 box for the right part of the key
vi pc1R{ 62, 54, 46, 38, 30, 22, 14, 6, 61, 53, 45, 37, 29, 21, 13, 5, 60, 52, 44, 36, 28, 20, 12, 4, 27, 19, 11, 3 };

//Permutation choice box-2 box for the left substring
vi pc2{ 13, 16, 10, 23, 0, 4, 2, 27, 14, 5, 20, 9, 22, 18, 11, 3, 25, 7, 15, 6, 26, 19, 12, 1, 40, 51, 30, 36, 46, 54, 29, 39,
          50,44, 32, 47, 43, 48, 38, 55, 33, 52, 45, 41, 49, 35, 28, 31 };

//Straight D-box
vi per = { 16, 7, 20, 21, 
                 	 29, 12, 28, 17, 
                  	 1, 15, 23, 26, 
                  	 5, 18, 31, 10, 
                 	 2, 8, 24, 14, 
                	 32, 27, 3, 9, 
                   	 19, 13, 30, 6, 
                  	 22, 11, 4, 25 };
                           
//This function converts a hexadecimal string into a binary string
string hextoBin(string s) 
{ 
    unordered_map<char, string> mp; 
    mp['0'] = "0000"; 
    mp['1'] = "0001"; 
    mp['2'] = "0010"; 
    mp['3'] = "0011"; 
    mp['4'] = "0100"; 
    mp['5'] = "0101"; 
    mp['6'] = "0110"; 
    mp['7'] = "0111"; 
    mp['8'] = "1000"; 
    mp['9'] = "1001"; 
    mp['A'] = "1010"; 
    mp['B'] = "1011"; 
    mp['C'] = "1100"; 
    mp['D'] = "1101"; 
    mp['E'] = "1110"; 
    mp['F'] = "1111"; 
    string binString = ""; 
    for (int i = 0; i < s.size(); i++) { 
        binString += mp[s[i]]; 
    } 
    return binString; 
}

//This function converts a bitset of variable sizes into a hexadecimal string
template< typename T> 
string bintoHex(bitset<sizeof(T)*8> h) 
{ 
    string s;
    for(int i=sizeof(T)*8-1;i>=0;i--){
    	s+=(h[i]+'0');
    }
    unordered_map<string, string> mp; 
    mp["0000"] = "0"; 
    mp["0001"] = "1"; 
    mp["0010"] = "2"; 
    mp["0011"] = "3"; 
    mp["0100"] = "4"; 
    mp["0101"] = "5"; 
    mp["0110"] = "6"; 
    mp["0111"] = "7"; 
    mp["1000"] = "8"; 
    mp["1001"] = "9"; 
    mp["1010"] = "A"; 
    mp["1011"] = "B"; 
    mp["1100"] = "C"; 
    mp["1101"] = "D"; 
    mp["1110"] = "E"; 
    mp["1111"] = "F"; 
    string hexString = ""; 
    for (int i = 0; i < s.length(); i += 4) { 
        string ch = ""; 
        ch += s[i]; 
        ch += s[i + 1]; 
        ch += s[i + 2]; 
        ch += s[i + 3]; 
        hexString += mp[ch]; 
    } 
    return hexString; 
} 

//This is a function to generate the sixteen subkeys 
void keyCreation(bitset<64> key){
        bitset<28> keyL;
        bitset<28> keyR;
        for(int i=0;i<28;i++){
        	keyL[27-i]=key[63-pc1L[i]];
        }
          for(int i=0;i<28;i++){
        	keyR[27-i]=key[63-pc1R[i]];
        }
        
        for(int i=0;i<16;i++){
        	 bitset<28> tempL;
       	 bitset<28> tempR;
       	 bitset<56> tempK;
       	 bitset<48> tempKF;
       	 tempL=keyL;
       	 tempR=keyR;
        	if(i==0 || i==1 || i==8 || i==15){
        		tempL=(tempL<<=1)|(tempL>>27);
        		tempR=(tempR<<=1)|(tempR>>27);
        	}
        	else{
        		tempL=(tempL<<=2)|(tempL>>26);
        		tempR=(tempR<<=2)|(tempR>>26);
        	}
        	keyL=tempL;
        	keyR=tempR;
        	for(int j=0;j<28;j++){
        		tempK[j]=tempR[j];
        		tempK[28+j]=tempL[j];
        	}
        	for(int j=0;j<48;j++){
        		tempKF[47-j]=tempK[55-pc2[j]];
		}
		//keyRound[i]='0';
		keyRound[i]=tempKF;

        }
}

//This function expands a 32 bit sequence into a 48 bit sequence and returns it as a bitset
bitset<48> expansion(bitset<32> &text){
	          
	bitset<48> expText;
	for(int i=0;i<48;i++){
		expText[47-i]=text[31-exp1[i]];
	}
	return expText;
}

//This function expands a 48 bit sequence into a 32 bit sequence and returns it as a bitset
bitset<32> compression(bitset<48> &text){
            
	bitset<32> compText;
	for(int i=0;i<8;i++){
		int row=0;
		int col=0;
		for(int j=i*6;j<i*6+6;j++){
			if(j%6==0){
				if(text[47-j]&1){
					row|=1<<1;
				}	
			}
			else if(j%6==5){
				if(text[47-j]&1){
					row|=1<<0;	
				}
			}
			else{
				if(text[47-j]&1){
					col|=1<<((4-(j-i*6)%4+4)%4);	
				}
			}
		}
		int Svalue=sBox[i][row][col];
		Svalue<<=(7-i)*4;
		compText|=Svalue;
	}
 	return compText;
                          
}

//This function permutates a 32 bit message according to the D-box
bitset<32> straightPermutation(bitset<32> &text){


	bitset<32> straightText;
	for(int i=0;i<32;i++){
		straightText[31-i]=text[32-per[i]];
	}
	return straightText;
}

//This is the function for feistel rounds
bitset<64> feistelRound(bitset<64> text){

	//Breaking the input into two parts 
	bitset<32> inputL,inputR;
	for(int i=0;i<32;i++){
		inputL[i]=text[32+i];
		inputR[i]=text[i];
	}
	bitset<32> tempL,tempR,temp;
	tempL=inputL;
	tempR=inputR;
	bitset<48> ER;
	
	//The 16 fistel rounds 
	for(int i=0;i<16;i++){
		temp=tempR;
		ER=expansion(tempR);
		ER ^=keyRound[i]; 
		tempR=compression(ER);
		tempR=straightPermutation(tempR);
		bitset<32> temp2=tempR^tempL;
		tempL=temp;
		tempR=temp2;
	}
	swap(tempL,tempR);
	
	//Combining the left and right part of the encrypted message into a 64 bit message 
	bitset<64>retset;
	for(int i=0;i<32;i++)retset[i]=tempL[i];
	retset<<=32;
	for(int i=0;i<32;i++)retset[i]=tempR[i];
	return retset;
	
}

//Function for initial permutation
bitset<64> initialPermutation(bitset<64> &bitInput){
	bitset<64> bitInputP;
	for(int i=0;i<64;i++){
		bitInputP[63-i]=bitInput[63-ip[i]+1];
	}
	return bitInputP;
}

//Function for fincal permutaion 
bitset<64> finalPermutation(bitset<64> &bitInput){
	bitset<64> bitInputP;
	for(int i=0;i<64;i++){
		bitInputP[63-i]=bitInput[63-fp[i]+1];
	}
	return bitInputP;
}
void init(){

	//Input string of 64 bits
	string input="0123456789ABCDEF";
	string binString=hextoBin(input);
	
	//Key of 64 bits
	string key="133457799BBCDFF1";
	cout<<"Initial Input: "<<input<<endl;
	cout<<"Key: "<<key<<endl;
	string binKey=hextoBin(key);
	bitset<64> bitInput(binString);
	bitset<64> bitKey(binKey);
	keyCreation(bitKey);
	bitset<64> bitInputP=initialPermutation(bitInput);
	bitInputP=feistelRound(bitInputP);
	bitInputP=finalPermutation(bitInputP);
	cout<<"After Encryption: ";
	cout<<bintoHex<ll>(bitInputP)<<endl;
	
	//Decryption [It is virtually the same algorithm as encryption with the subkeys reversed]
	//Reversing the vector of subkeys
	reverse(keyRound.begin(),keyRound.begin()+16);
	bitInputP=initialPermutation(bitInputP);
	bitInputP=feistelRound(bitInputP);
	bitInputP=finalPermutation(bitInputP);
	cout<<"After Decryption: ";
	cout<<bintoHex<ll>(bitInputP)<<endl;

}

int main(){
	init();
}




















