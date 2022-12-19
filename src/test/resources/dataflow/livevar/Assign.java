class Assign {

    int assign(int a, int b, int c) {
        int d = a + b;//-d +a+b #ab
        b = d;//-b +d #ad
        c = a;//-c +a #ab
        return b;//+b #b
    }
}
