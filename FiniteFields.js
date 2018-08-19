class FiniteField{
    constructor(polynomial){
        var time = Date.now();
        this.field = polynomial;
        this.degree = FiniteField.intLog2(polynomial);
        this.size = 1<<this.degree;
        this.reduction = polynomial^this.size;
        this.p2s = this.powersOf2();
        this.degrees = this.logarithmsOf2();
        this.allPowers = this.makePowers();
        console.log(Date.now()-time);
        var d = {};
        for(var i = 0;i<this.allPowers.length;i++){
            d[this.allPowers[i]]=i;
        }
        this.polyToPower = d;

        this.irreducible = this.getIrreducibles();
        console.log(Date.now()-time);
    }
    // precompute
     // O(n)
    powersOf2(){
        var N = [];
        for(var n = 0;n<=32;n++){
            N.push(1<<n);
        }
        return N;
    }
    // precompute
     // O(2^n)
    logarithmsOf2(){
        var ret = [0];
        for(var n = 0;n<this.degree;n++){
            var start = 1<<n;
            var end = 1<<(n+1);
            for(var i = start;i<end;i++){
                ret.push(n);
            }
        }
        return ret;
    }
    // precompute
     // O(2^n^2)
    getIrreducibles(){
        var isIrr = new Array(this.size).fill(1);
        for(var i = 4;i<this.size;i++){  
            isIrr[i] = i&1;                                 // divisible by x 
        }
        for(var i = 3;i<this.size;i+=2){
            var lastJ = this.p2s[this.degree-this.degrees[i]];
            var di = this.degrees[i];
            for(var j = 3;j<lastJ;j+=2){             
                isIrr[this._mult(i,j,di,this.degrees[j])]=0;
            }
        }
        return isIrr;
    }
    // precompute all powers
    // O(2^n)
    makePowers(){
        if(this.degree < 2){
            return [1];
        }
        var bits = 1;
        var maximal = this.size;
        var ret = new Array(maximal);
        ret[0] = 1;
        for(var n = 1;n<maximal;n++){
            bits = bits<<1;
            if(bits >= maximal){
                bits ^= this.field;
            }
            ret[n] = bits;
        }
        var found = false;
        for(var i = 1;i<ret.length;i++){
            if(ret[i] == 1){
                ret = ret.slice(0,i);
                break;
            }

        }
        return ret;
    }
    // helper
    static mod(a,n){
        var a = a%n;
        if(a<0)
            return a+n;
        return a;
    }
    static intLog2(a){
        return Math.max(0,Math.floor(Math.log2(a)));
    }
    
    get period(){
        return this.allPowers.length;
    }
    get isPrimitive(){
        return this.isIrreducible && this.period == (this.size-1);
    }
    get isIrreducible(){
        return this.factor(this.field).length == 1;
    }

    toPolynomial(power){
        var p = FiniteField.mod(power,this.period);
        return this.allPowers[p];
    }
    toExponential(polynomial){
        return this.polyToPower[this.reduce(polynomial)];
    }

    add(A,B){
        return this.reduce(A^B);
    }
    sub(A,B){
        return this.add(A,B);
    }
   
    mult(A,B){
        if(A==0 || B==0)  // one of them is zero
            return 0;
        if(A == 1)
            return this.reduce(B);
        if(B == 1)
            return this.reduce(A);
        var power = this.toExponential(A)+this.toExponential(B);
        if(!isNaN(power))
            return this.toPolynomial(power);
        // field is not primitive, some polys cannot be expressed as powers
        var newBits = 0;
        var a = this.reduce(A);
        var b = this.reduce(B);
        for(var i = 0;i<=this.degrees[a];i++){
            if(a&this.p2s[i]){
                for(var j = 0;j<=this.degrees[b];j++){
                    if(b&this.p2s[j]){
                        newBits^=this.p2s[i+j]; 
                    }
                }
            }
        }
        return this.reduce(newBits);
    }
    _mult(a,b,da,db){
        var p = this.polyToPower[a]+this.polyToPower[b];
        if(!isNaN(p))
            return this.allPowers[p%this.period];
        // field is not primitive, some polys cannot be expressed as powers
        var newBits = 0;
        for(var i = 0;i<=da;i++){
            if(a&this.p2s[i]){
                for(var j = 0;j<=db;j++){
                    if(b&this.p2s[j]){
                        newBits^=this.p2s[i+j]; 
                    }
                }
            }
        }
        return newBits;
    }
    pow(A,n){
        if(A == 0)
            return 0;
        if(A == 1)
            return 1;
        if(n == 0)
            return 1;
        if(n == 1)
            return this.reduce(A);
    
        var power = this.toExponential(A);
        if(!isNaN(power))
            return this.toPolynomial(power*n);
        // field is not primitive
        var ret = A;
        if(n>0){
            var m = 1;
            for(var i = 1;i<Math.log2(n);i++){      // exp by squares
                ret = this.mult(ret,ret); m*=2;
            }
            for(var i = m;i<n;i++){
                ret = this.mult(ret,A); m++;
            }
            return ret;
        }else{
            return this.pow(this.div(1,A),-n);
        }
    }
    div(A,B){
        if(B==0)  // div zero
            throw "Division by zero";
        if(A == 0)
            return 0;
        if(B == 1)
            return this.reduce(A);
        var power = this.toExponential(A)-this.toExponential(B);
        if(!isNaN(power))
            return this.toPolynomial(power);
        // field is not primitive, A or B not expressible as a power
        // naive, iterate through all polys to find the correct one
        for(var i = 0;i<this.degrees.length;i++){
            if(this.mult(B,i) == A)
                return i;
        }
        // wut?
        throw "WUT? division";
    }

    factor(A){
        return this._factor(A,this.degrees[A]);
    }
    _factor(a,d){
        if(a<4 || this.irreducible[a])  // a+1,a,1,0 or irreducible
            return [a];
        if(!(a&1))          // divisible by a
            return this._factor(a>>1,d-1).concat([2]);

        var maxDeg = Math.ceil(d/2);
        for(var n1 = 1;n1<=maxDeg;n1++){    // go through all degrees necessary
            var start1 = this.p2s[n1]; //                  ex a
            var end1 = this.p2s[n+1];   //                  ex a2
            var n2 = this.degree-n1;    // this
            var start2 = this.p2s[n2];  //   ex a7     
            var end2 = this.p2s[n2+1];    //   ex a8   -> a*a7 = a8
            for(var i = start1;i<end1;i++){   // all polys of that degree 1
                for(var j = start2;j<end2;j++){   // all polys of that degree 2, so that degree 1+2 = this.degree
                    if(this._mult(i,j,n1,n2)==a){
                        return this._factor(j,n2).concat([i]);  // j > i, thus j might be factorizable
                    }
                }
            }
        }
        // irreducible
        return [a];
    }
    reduce(A){
        if(A < this.p2s[this.degree])    // avoid degree calculation
            return A;
        var result = A&(this.size-1);    
        var da = Math.floor(Math.log2(A));
        for(var i = this.degree;i<da;i++){
            if(A&this.p2s[i]){
                result ^= this.toPolynomial(i);
            }
        }
        return result;
    }

    // create a finite field from the expression.
    // should not contain multiplications or divisions
    static parseField(expression){
        return new FiniteField(FiniteField.parsePolynomial(expression));
    }

    // uses math.js to parse the expression tree
    parseExpression(expression){
        if(expression == "0" || expression =="" || expression == null)
            return 0;
        var expr = expression.replace("^-","@");
        if(expr[0] == "-")  // drop first -
            expr = expr.substring(1,expr.length-1);
        expr = expr.replace("(-","(");  // drop parenthesis first -
        expr = expr.replace("-","+");   // change all - to +
        expr = expr.replace("@","^-");  // except powers
        var expr0 = math.parse(expr);
        
        return this._solveExpr(expr0);
    }
    _solveExpr(node){
        if(node.type == "SymbolNode")
            return 2;
        if(node.type == "ConstantNode"){
            return node.value%2;
        }
        if(node.type == "OperatorNode"){
            switch(node.op){
                case "^":
                    if(node.args[1].type == "ConstantNode"){
                        return this.pow(this._solveExpr(node.args[0]),node.args[1].value);
                    }else{
                        return this.pow(this._solveExpr(node.args[0]),-node.args[1].args[0].value);
                    }
                case "*":
                    return this.mult(this._solveExpr(node.args[0]),this._solveExpr(node.args[1]));
                case "/":
                    return this.div(this._solveExpr(node.args[0]),this._solveExpr(node.args[1]));
                case "+":
                    return this.add(this._solveExpr(node.args[0]),this._solveExpr(node.args[1]));
            }
        }     
        if(node.type == "ParenthesisNode"){
            return this._solveExpr(node.content);
        }       
    }

    static parsePolynomial(expression){
        if(expression == "0" || expression =="" || expression == null)
            return 0;
        var expr = expression
        if(expr.substr(0,1) == "-")  // drop first -
            expr = expr.substring(1,expr.length-1);
        expr = expr.replace("(-","(");  // drop parenthesis first -
        expr = expr.replace("-","+");   // change all - to +
        console.log(expr);
        var expr0 = math.parse(expr);
        console.log(expr0);
        
        return FiniteField._solvePolynomial(expr0);
    }
    static _solvePolynomial(node){
        if(node.type == "SymbolNode")
            return 2;
        if(node.type == "ConstantNode"){
            return node.value%2;
        }
        if(node.type == "OperatorNode"){
            switch(node.op){
                case "^":
                    if(node.args[1].type == "ConstantNode")
                        return (1<<node.args[1].value);
                    return FiniteField.empty();
                case "+":
                    return FiniteField._solvePolynomial(node.args[0])^FiniteField._solvePolynomial(node.args[1]);
            }
        }     
        if(node.type == "ParenthesisNode"){
            return FiniteField._solvePolynomial(node.content);
        }       
    }

    toString(isHtml){
        var html = "";
        if(isHtml){
            html+= '<span class="field" data-num="'+this.field+'">';
            html+="&Gopf;&Fopf;(2<sup>"+this.degree+"</sup>)";
            html+=this.polyToString(this.field,isHtml);
            html+="</span>";
        }else{
            html+="GF(2^"+this.degree+") "+this.polyToString(this.field,isHtml);
        }
        return html;
    }

    polyToString(poly,isHtml,isDeg){
        var deg = FiniteField.intLog2(poly);
        if(isDeg){
            deg = poly;
            poly = null;
        }
        if(isHtml){
            var html = '<span class="poly" data-num="'+poly+'">';
            if(poly == null){
                html+="a<sup>"+deg+"</sup>";
            }else{
                for(var n = deg;n>=0;n--){
                    if(poly & this.p2s[n]){
                        if(n>0){
                            html+= "a"
                            if(n>1){
                                html+="<sup>"+n+"</sup>";
                            }
                        }else{
                            html+= "1";
                        }
                        html+="+";
                    }
                }
            }
            html = html.substr(0,html.length-1);
            html+="</span>";
        }else{
            var html = "";
            if(poly == null){
                html+="a^"+deg;
            }else{
                for(var n = deg;n>=0;n--){
                    if(poly & this.p2s[n]){
                        if(n>0){
                            html+= "a"
                            if(n>1){
                                html+="^"+n;
                            }
                        }else{
                            html+= "1";
                        }
                        html+="+";
                    }
                }
            }
            html = html.substr(0,html.length-1);
        }
        return html;
    }

    polyToBitString(poly,deg,isHtml){
        if(isHtml){
            var html = '<div class="bitstring">';
            for(var i = deg;i>=0;i--){
                var bit = ((poly>>i)&1)
                html+='<span class="bit'+bit+'">'+bit+'</span>';
            }
            return html+"</div>";
        }
        if(deg == null)
            deg = FiniteField.intLog2(poly);
        var bits = poly.toString(2);
        while(bits.length<=deg){
            bits = "0"+bits;
        }
        return bits;
    }

    toBitString(polynomial,isHtml){
        return this.polyToBitString(polynomial,this.degree-1,isHtml);
    }

}