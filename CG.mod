param nSET integer >= 0, default 0;
param nT:=50;
param nK:=30;
param nO:=3;
param nD:=10;

set Orig:= 1..nO ordered;
set Dest:= 1..nD ordered;
set K:=1..nK; 
set T:=1..nT ordered;
set VS;
set VT;


param LAT1{Orig};
param LAT2{Dest};
param LON1{Orig};
param LON2{Dest};

param o{j in Orig}:=ord(j);
param p{j in Dest}:=ord(j);

param TW{T}; 	# target delivery time of each task
param Depot{T};
param Client{T};
param QTY{T};

param Rent_period{K}; 	# Rent period length of each truck
param Supplier{K};
param Capacity{K};
param Cost{K};           #cost per unit time
param dv{i in K};
param F_cost{i in K}:=Cost[i]*Rent_period[i];  #fixed cost

set Z within {T,Orig} := {i in T, j in Orig: Depot[i] = j};
set ZZ within {T,Dest} := {i in T, j in Dest: Client[i] = j};
set Z1 within {T,Orig,Dest}:={i in T,j in Orig, k in Dest: Depot[i] = j and Client[i] = k};

param Client_lat{(i,j) in ZZ}:= LAT2[p[j]];
param Client_lon{(i,j) in ZZ}:= LON2[p[j]];
param Depot_lat{(i,j) in Z}:= LAT1[o[j]];
param Depot_lon{(i,j) in Z}:= LON1[o[j]];

param l1{i in T}:=sum{j in Orig:(i,j) in Z}Depot_lat[i,j];
param l2{i in T}:=sum{j in Orig:(i,j) in Z}Depot_lon[i,j];
param l3{i in T}:=sum{j in Dest:(i,j) in ZZ}Client_lat[i,j];
param l4{i in T}:=sum{j in Dest:(i,j) in ZZ}Client_lon[i,j];

param dur{i in T}:=			#time required to finish a task 
acos(cos((1/57.29578)*(90-l1[i]))*cos((1/57.29578)*(90-l3[i]))+sin((1/57.29578)*(90-l1[i]))*sin((1/57.29578)*(90-l3[i]))*cos((1/57.29578)*(l2[i]-l4[i])))*6371*0.7;

param d{i in T,j in T}:=     #time required to go from end of task i to start of task j
acos(cos((1/57.29578)*(90-l3[i]))*cos((1/57.29578)*(90-l1[j]))+sin((1/57.29578)*(90-l3[i]))*sin((1/57.29578)*(90-l1[j]))*cos((1/57.29578)*(l4[i]-l2[j])))*6371*0.7;

set Ed within {T,T}:={i in T, j in T:ord(i)<ord(j)};

set EE within {T,T}:= {i in T, j in T:ord(i)<ord(j)and (TW[j] <= TW[i]+d[i,j]+dur[j]) or (TW[j] > TW[i]+d[i,j]+dur[j]+60)};		#Conflict graph

set G:= Ed diff EE;       #Complementary graph

set Ef within {T,T}:={i in T, j in T:ord(i)=ord(j)};


set ADJ {i in T} :=			#Adjacent nodes of i
{j in T: (i,j) in G };


set ALLPATH default{};                 #set of all feasible routes

set PATHSET{ALLPATH};
param pathnumcount default 0; 
param taskcount default 1; 
param Path_time {ALLPATH}; 

set ALLPATH1 default{};                 #set of all feasible routes

set PATHSET1{ALLPATH1};
param pathnumcount1 default 0; 
param taskcount1 default 1; 
param Path_time1 {ALLPATH1}; 

set ALLPATH4 default{};                 #set of all feasible routes
param nbr{i in T,j in ALLPATH4};			#1, if task i is in task set j
set PATHSET4{ALLPATH4};
param pathnumcount4 default 0; 
param Path_time4 {ALLPATH4};

set COMM  default {};	
set ALLPATH3 ordered := ALLPATH1 diff COMM;
set PATHSET3{ALLPATH3};
param Path_time3 {ALLPATH3};
			#1, if task i is in task set j

set ALLPATH2 default{};                 #set of all feasible routes
set PATHSET2{ALLPATH2};
param pathnumcount2 default 0; 
param taskcount2 default 1; 
param Path_time2 {ALLPATH2}; 

# ----------------------------------------
# Restricted Master Problem
# ----------------------------------------

param nRun integer >=0 , default 0;
suffix dunbdd;
set RMP{0..nRun} default {};
set PSP{0..nRun} default {};
param nmbr{i in T,j in RMP[nRun]};
param nmbr1{i in T,j in PSP[nRun]};
var y {i in K,j in RMP[nRun]}>=0, <=1, integer ; #binary;    # = 1 if taskset j in is selected for truck i. 0 otherwise.
 
minimize Total_cost:                  

sum {i in K,j in RMP[nRun]}y[i,j]*Cost[i]*(Rent_period[i]*(1-dv[i])+Path_time4[j]*(dv[i]));
 
subj to Fill {i in T}:
   sum {k in K,j in RMP[nRun]} nbr[i,j] * y[k,j] = 1;
   
subj to Assign {i in K}:
   sum {j in RMP[nRun]} y[i,j] <= 1;   
   
#subj to Time {i in T, k in K}:
 #  sum{j in RMP[nRun]}y[k,j]*nbr[i,j]<=1;     

subj to Time {i in K}:
   sum{j in RMP[nRun]}y[i,j]*(Path_time4[j] - Rent_period[i])<=0;  
   

# ----------------------------------------
# Pricing Problem
# ----------------------------------------

param kk symbolic within K;

param price1 {K,1..nRun} <=0.00000001 default 0;

param price2 {T,1..nRun}  default 0.0;  #>=-0.00000001

param price3 {K,1..nRun} <=0.00000001 default 0.0;

#param price3 {T,K,1..nRun} <=0.00000001 default 0.0;

var Use {PSP[nRun],K} >=0, <=1, integer;

minimize Reduced_Cost:  
price1[kk,nRun] +
sum{j in PSP[nRun],i in T}(price2[i,nRun]*nbr[i,j])*Use[j,kk]+
sum {j in PSP[nRun]}price3[kk,nRun]*(Path_time4[j] - Rent_period[kk])*Use[j,kk]-
(sum {j in PSP[nRun]}Use[j,kk]*Cost[kk]*(Rent_period[kk]*(1-dv[kk])+Path_time4[j]*(dv[kk])));


subj to Assign_Limit:  
   sum {j in PSP[nRun]} Use[j,kk] =1;
	

subj to Assign_Time:  
   sum {j in PSP[nRun]} Use[j,kk]*(Path_time4[j]- Rent_period[kk])<=0;









