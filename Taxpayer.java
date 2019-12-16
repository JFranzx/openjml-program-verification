
/* 
  This assignment illustrates how specifications (invariants and 
  preconditions)  written in a formal language can help in removing 
  errors in code. 
 */

class Taxpayer {


 /* isFemale is true iff the person is female */
 boolean isFemale;

 /* isMale is true iff the person is male */
 boolean isMale;

 int age; 

 boolean isMarried; 

 /* Reference to spouse if person is married, null otherwise */
 /*@ nullable @*/ Taxpayer spouse; 

 /* Constant default income tax allowance */
 static final int DEFAULT_ALLOWANCE = 5000;

 /* Constant income tax allowance for Older Taxpayers over 65 */
 static final  int ALLOWANCE_OAP = 7000;

 /* Income tax allowance */
 int tax_allowance; 

 int income; 
 /*@ nullable @*/ Taxpayer mother;
 /*@ nullable @*/ Taxpayer father;


//@ invariant this.isMarried <==> this.spouse != null;
//@ invariant age >=0 && age <= Integer.MAX_VALUE;
//@ invariant this.tax_allowance >= 0 && tax_allowance <= Integer.MAX_VALUE;
//@ invariant  this.income >= 0 && this.income <= Integer.MAX_VALUE;
 
//part1
//@ invariant this.isFemale <==> !this.isMale;
//@ invariant (this.spouse!= null) ==> (this.isMale <==> this.spouse.isFemale);
//@ invariant (this.spouse != null) ==> (this.spouse != this.mother && this.spouse != this.father && this.spouse != this);
//@ invariant (this.spouse != null) ==> this.spouse.spouse == this;
//@ invariant this.isMarried ==> age >= 18 && spouse.age >= 18;
//@ invariant mother != this && father != this;
 //part2
 //part3
//@ invariant (!isMarried && age<65) ==> tax_allowance == DEFAULT_ALLOWANCE;
//@ invariant (!isMarried && age >= 65) ==> tax_allowance == ALLOWANCE_OAP;
/*@ invariant isMarried ==> (
 		((age < 65 && spouse.age < 65) <==> (tax_allowance + spouse.tax_allowance == 10000))
		||
		(((age < 65 && spouse.age >= 65)||(age >= 65 && spouse.age < 65)) <==> (tax_allowance + spouse.tax_allowance == 12000))
		||
		((age >= 65 && spouse.age >= 65) <==> (tax_allowance + spouse.tax_allowance == 14000))
		);
		
@*/


 
 Taxpayer(boolean babyboy, Taxpayer ma, Taxpayer pa) {
   age = 0;
   isMarried = false;
   this.isMale = babyboy;
   this.isFemale = !babyboy;
   mother = ma;
   father = pa;
   spouse = null;
   income = 0;
   tax_allowance = DEFAULT_ALLOWANCE;
   
 } 


 //@ requires new_spouse != null;
//@ requires new_spouse != null && !new_spouse.isMarried;
//@requires new_spouse.isFemale <==> this.isMale;
//@requires !this.isMarried;
//@ requires new_spouse != this && new_spouse != this.mother && new_spouse != this.father;
//@ requires new_spouse.mother != this && new_spouse.father != this;
//@ requires new_spouse.age >= 18 && age >= 18;
void marry(Taxpayer new_spouse) {
	 
	 spouse = new_spouse;
	 spouse.spouse = this;
	 spouse.isMarried = true;
	 isMarried = true;
}
 


//@ requires isMarried;
 void divorce() {
	 if(spouse.age>=65) spouse.tax_allowance = ALLOWANCE_OAP;
	 else spouse.tax_allowance = DEFAULT_ALLOWANCE;
	 spouse.isMarried=false;    //+ static check
	 spouse.spouse = null;
	 spouse = null;
	 isMarried = false;
	 if(age >= 65) tax_allowance = ALLOWANCE_OAP;
	 else tax_allowance = DEFAULT_ALLOWANCE;
 }

 /* Transfer part of tax allowance to own spouse */
 /*@ 
 requires change >= 0 && change <= tax_allowance;
 requires isMarried;
 requires change + spouse.tax_allowance <= Integer.MAX_VALUE;
@*/
 void transferAllowance(int change) {
  tax_allowance = tax_allowance - change;
  spouse.tax_allowance = spouse.tax_allowance + change;
 }


//@ requires age+1 <= Integer.MAX_VALUE;
//@ requires age+1 == 65 ==> tax_allowance + (ALLOWANCE_OAP - DEFAULT_ALLOWANCE) <= Integer.MAX_VALUE;
 void haveBirthday() {
	age++;
	 if(age==65) tax_allowance += (ALLOWANCE_OAP - DEFAULT_ALLOWANCE);
 }

}

