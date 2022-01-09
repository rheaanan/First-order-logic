import re
import sys
import copy
import time
time1 = 0

class knowledge_base:
    def __init__(self):
        self.sentences = []
        self.in_cnf = []
        self.truths = set()
        self.KB_dict = {}
        self.sen_dict = {}
        self.queries_dict = {}
        self.visited = {}

        self.timeout = 10

    def split_into_args(self, literal):
        #print("literal", literal)
        s_split = literal.split('(')
        args = s_split[1].rstrip(') ').split(',')
        if len(args)>1:
            return s_split[0].strip(), args
        else:
            return s_split[0].strip(), args

    def isVariable(self, x):
        if isinstance(x,str) and x[0].isalpha() and x[0].islower():
            return True
        else:
            False

    def isCompound(self, x):
        if isinstance(x, tuple):
            return True
        else:
            return False

    def isList(self, x):
        if isinstance(x, list):
            return True
        else:
            return False

    def unify_var(self,var, x, theta):
        if var in theta:
            return self.unification(theta[var], x, theta)
        elif x in theta:
            return self.unification(var, theta[x], theta)
        else:
            if not self.isVariable(x):
                theta[var] = x
            return theta


    def unification(self, x, y, theta):
        #print("x and y" , x,y)
        if 'fail' in theta:
            return theta
        if x == y:
            return theta
        elif self.isVariable(x):
            return self.unify_var(x,y,theta)
        elif self.isVariable(y):
            return self.unify_var(y,x,theta)
        elif self.isCompound(x) and self.isCompound(y):
            return self.unification(x[1],y[1],self.unification(x[0],y[0],theta))
        elif self.isList(x) and self.isList(y):
            return self.unification(x[1:],y[1:],self.unification(x[0], y[0], theta))
        else:
            theta['fail'] = 1
            return theta


    def negate(self, sen):
        res = []
        if sen[0] == '~':
            res.append(sen[1:])
        else:
            res.append('~' + sen)
        return "".join(res)

    def negate_q(self, pred):
        function = ""
        args = pred[1]
        if pred[0][0] == '~':
            function = str(pred[0][1:])
        else:
            function = "".join('~' + pred[0])

        return (function, args)

    def store_queries(self,sentence, sen_no):
        sen_arr = []
        pred, args = self.split_into_args(sentence)
        sen_arr.append((pred, args))
        self.queries_dict[sen_no] = sen_arr

    def add_to_KB_dict(self, pred ,sen_no):
        if pred not in self.KB_dict:
            self.KB_dict[pred] = []
        if sen_no not in self.KB_dict[pred]:
            self.KB_dict[pred].append(sen_no)

    def add_no_to_args(self,args, sen_no):
        for i in range(0,len(args)):
            if self.isVariable(args[i]):
                args[i] = "".join([args[i],str(sen_no)])

    def remove_from_KB(self, pred, sen_no):
        del self.sen_dict[sen_no]
        self.KB_dict[pred].pop()
        if len(self.KB_dict[pred]) == 0:
            del self.KB_dict[pred]

    def store(self, sentence, sen_no):
        sen_arr = []
        if "=>" in sentence:
            split_sentence = sentence.split('=>')
            for i in split_sentence[0].split():
                if i != '&':
                    negated = self.negate(i)
                    pred, args = self.split_into_args(negated)
                    self.add_no_to_args(args, sen_no)
                    sen_arr.append((pred,args))
                    self.add_to_KB_dict(pred,sen_no)

            pred, args = self.split_into_args(split_sentence[-1])
            self.add_no_to_args( args, sen_no)
            sen_arr.append((pred, args))
            self.add_to_KB_dict(pred,sen_no)


        else:
            pred, args = self.split_into_args(sentence)
            sen_arr.append((pred, args))
            self.add_to_KB_dict(pred, sen_no)


        self.sen_dict[sen_no] = sen_arr

    def going_into_loop(self, path, depth):                         #! implement this properly
        return False

    def find_in_sentence(self, sentence, func):
        for i in range (0,len(sentence)):
            if sentence[i][0] == func:
                return i
        return -1

    def substitute_theta(self, sentence, pos, theta):
        sentence.pop(pos)
        for pred in sentence:
            for i in range(0,len(pred[1])):
                if pred[1][i] in theta:
                    pred[1][i]=theta[pred[1][i]]

    def concat_parent(self, negated_q, p_query, curr_sentence):
        for i in range(0, len(p_query)):
            if p_query[i]==negated_q:
                continue
            else:
                curr_sentence.append(p_query[i])

    def check_if_already_comp(self, query, sen_no):
        compressed = str(query)
        if compressed in self.visited:
            if sen_no in self.visited[compressed]:
                return True
        else:
            self.visited[compressed] = []
        self.visited[compressed].append(sen_no)
        return False



    def prove_its_true(self, query, depth, parent):
        output = False
        found_sentences = []
        #print("depth",depth)
        #print(time1)
        if time.time() - time1 > 5:
            return False

        if len(query)==0:              ## check len(query) when its empty
            return True
        depth += 1
        if depth > 0:
            parent_length = len(parent[:depth -1])
            if not self.going_into_loop(parent, parent_length):
                for pred in query:
                    found_sentences = []
                    negated_q = self.negate_q(pred)
                    #print("searching for double negated query predicates in query", negated_q)
                    if negated_q[0] in self.KB_dict:
                        found_sentences.extend(self.KB_dict[negated_q[0]])
                    else:
                        break
                    found_sentences.sort(reverse=True)
                    #print("found_sentence", found_sentences)
                    for sen in found_sentences:
                        curr_sentence = copy.deepcopy(self.sen_dict[sen])
                        pos = self.find_in_sentence(curr_sentence,negated_q[0])
                        if self.check_if_already_comp(query,sen):
                            #print("already seen pairs", query,sen)
                            return False
                        if pos!= -1:
                            #print("calling unification with",curr_sentence[pos],negated_q)
                            theta = self.unification(curr_sentence[pos],negated_q,{})
                            if 'fail' not in theta:
                                #print("calling substitue theta with", curr_sentence, pos, theta)
                                self.substitute_theta(curr_sentence, pos, theta)
                                #print("sentence after substitution", curr_sentence)
                                parent.append(sen)

                                #print("calling concat with ", sen, pred, curr_sentence)
                                parent_query = copy.deepcopy(query)
                                self.concat_parent(pred, parent_query, curr_sentence)
                                #print("sentence after concat", curr_sentence)
                                if(len(curr_sentence) == 0 or self.prove_its_true(curr_sentence, depth, parent) == True):
                                    return True

                        else:
                            #print("!!shouldnt reach here couldnt find the predicate in the sentence")
                            return False
                    #print("can't unify anything from KB")
                return False

                    #pos = self.find_in_sentence(curr_sentence, negated_q[0])
                    #self.unification(KB.sen_dict[i],negated_q)

def main():
    KB = knowledge_base()
    f = open("input.txt", "r")
    f2 = open("output.txt", "w")
    number_of_queries = int(f.readline().rstrip())
    queries = []
    KB = knowledge_base()
    for i in range(0,number_of_queries):
        queries.append(f.readline().rstrip())
        KB.store_queries(KB.negate(queries[i]), i)                              # storing negated queries do not negate again
    #print(queries)
    number_of_sentences = int(f.readline().rstrip())

    for i in range(number_of_sentences):
        KB.sentences.append(f.readline().rstrip())
        #print("sentence passed", KB.sentences[i])
        KB.store(KB.sentences[i], i)
    #print(KB.sen_dict)
    #print(KB.KB_dict)
    #print(KB.queries_dict)
    #theta ={}
    #theta_final = KB.unification(KB.sen_dict[1][1], KB.queries_dict[0][0],theta)
    #print("theta works", theta_final)

    for i in range(0,number_of_queries):
        KB.sen_dict[101] = KB.queries_dict[i]                                                 # adding query sentence to KB
        KB.add_to_KB_dict(KB.queries_dict[i][0][0],101)
        KB.visited = {}
        global time1
        time1 = time.time()
        try:
            final_output = KB.prove_its_true(KB.queries_dict[i],1,[])
        except:
            final_output = False

        #print("final_output", final_output)
        if final_output == False:
            f2.writelines("FALSE")
        else:
            f2.writelines("TRUE")
        #print("after adding to KB")
        KB.remove_from_KB(KB.queries_dict[i][0][0],101)
        #print("after removing from KB")
        if (i != number_of_queries - 1):
            f2.writelines("\n")


if __name__ == "__main__":
    main()





