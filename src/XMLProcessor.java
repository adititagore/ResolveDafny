import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;

import org.w3c.dom.*;


public class XMLProcessor {

	ArrayList<String> var_decld = new ArrayList<String>();
	ArrayList<String> fun_decld = new ArrayList<String>();

	FileWriter fstream; 
	BufferedWriter out;
	int c =0, i =0;

	static int set_object = 0, set_integer = 0, string_object = 0, string_integer = 0;

	public void ProcessXmlsFromDirectory(String files, String DirName)
	{		
		try
		{
			String wholepath = DirName + files;
			//System.out.println("The whole path is "+wholepath);

			File file = new File(wholepath);
			DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
			dbf.setIgnoringElementContentWhitespace(true);
			dbf.setNamespaceAware(true);
			dbf.setIgnoringComments(true);

			DocumentBuilder db = dbf.newDocumentBuilder();
			Document doc = db.parse(file);

			doc = db.parse(file);
			doc.normalizeDocument();

			Node root = doc.getDocumentElement();
			// remove whitespace nodes
			root.normalize();
			removeWhitespace(root);

			//open file for writing

			fstream = new FileWriter("C:\\MY_STUFF\\research\\VC_Dafny\\" + files.substring(0, (files.length() - 4)) + ".dfy");
			out = new BufferedWriter(fstream);


			Node formula = root.getLastChild();		

			Node implies = formula.getFirstChild();
			//			System.out.println(implies.toString());
			//			System.out.println(implies.getFirstChild().toString());			

			get_types_of_objects(doc);

			out.write("class Client<T>{");
			out.newLine();
			declare_vars(doc);
			//declare_funs(doc);

			declare_funs_dynamic(doc);

			out.write("method formula() {");

			restrictions_body(doc);
			implicit_funs_body(doc);
			explicit_funs_body(doc);
			out.newLine();

			declare_inbuiltfuns_and_lemmas(doc);
			//declare_other_lemmas(doc);

			NodeList facts = implies.getFirstChild().getChildNodes();

			Node obligation = implies.getLastChild();

			int f = facts.getLength();

			//findMethods(doc);

			if (f> 0) 
			{
				for (int j = 0; j < f; j++)
				{
					out.newLine();
					out.write("assume ");
					traverseTree(facts.item(j) , doc);
					out.write(";");
				}
			}//end if (f> 0)

			out.newLine();
			out.write("assert ");
			traverseTree(obligation, doc);
			out.write(";");			
			out.newLine();
			out.write("} }");
			out.newLine();
			out.close();

		}
		catch (Exception e) 
		{
			e.printStackTrace();  
		}
	}//end ProcessXMLsFromDirectory

	public void declare_vars(Document doc) throws IOException
	{

		NodeList vars = doc.getElementsByTagName("symbol");
		int numSymbols = vars.getLength();

		out.newLine();	


		for (int i = 0; i < numSymbols; i++) 
		{
			//System.out.println(vars.item(i).getParentNode().getNodeName().toString()); 
			if(!(vars.item(i).getParentNode().getNodeName().toString().equals("dot")))
			{
				String symbol = vars.item(i).getFirstChild().getTextContent();
				//System.out.println("symbol: "+symbol);
				String type = vars.item(i).getAttributes().getNamedItem("type").getNodeValue();

				if (symbol.contains("."))
				{
					int index = symbol.indexOf(".");	                
					symbol = symbol.substring(0, index) + "_" + symbol.substring(index + 1);
					// System.out.println(symbol);
				}
				if (!(var_decld.contains(symbol)))
				{
					var_decld.add(symbol);

					if(type.equals("finiteset(object)"))
					{

						out.write("var "+ symbol + " : set<T>;");
						out.newLine();
					}

					else if (type.equals("object") || type.equals("character"))
					{
						out.write("var "+ symbol + " : T;");
						out.newLine();
					}

					else if (type.equals("integer"))
					{
						out.write("var "+ symbol + " : int;");
						out.newLine();
					}
					else if (type.equals("string(object)") || type.equals("string(character)"))
					{
						out.write("var "+ symbol + " : seq<T>;");
						out.newLine();
					}
					else if (type.equals("string(integer)"))
					{
						out.write("var "+ symbol + " : seq<int>;");
						out.newLine();
					}
					else if (type.equals("boolean"))
					{
						out.write("var "+ symbol + " : bool;");
						out.newLine();
					}
				}

			}//end for
		}//end if
		out.newLine();	

		NodeList dots = doc.getElementsByTagName("dot");
		int numDots = dots.getLength();
		//System.out.println("numDots"+numDots);


		for (int i = 0; i < numDots; i++) 
		{
			String type = dots.item(i).getAttributes().getNamedItem("type").getNodeValue();

			int numChild = dots.item(i).getChildNodes().getLength();
			String dot_var = "";
			if(numChild <=2)
			{
				String p1 = dots.item(i).getFirstChild().getTextContent();
				String p2 = dots.item(i).getLastChild().getTextContent();
				//	System.out.println("p1: "+p1);
				//	System.out.println("p2: "+p2);
				dot_var = p1+"_"+p2;
			}
			else
			{
				String p1 = dots.item(i).getFirstChild().getTextContent();
				String p2 = dots.item(i).getFirstChild().getNextSibling().getTextContent();
				String p3 = dots.item(i).getLastChild().getTextContent();

				dot_var = p1+"_"+p2+"_"+p3;
			}			

			if (dot_var.contains("."))
			{
				int index = dot_var.indexOf(".");	                
				dot_var = dot_var.substring(0, index) + "_" + dot_var.substring(index + 1);
			}
			if (!(var_decld.contains(dot_var)))
			{
				var_decld.add(dot_var);
				if (type.equals("string(object)")|| type.equals("string(character)"))
				{
					out.write("var "+ dot_var + " : seq<T>;");
				}
				if (type.equals("string(integer)"))
				{
					out.write("var "+ dot_var + " : seq<int>;");
				}
				else if (type.equals("integer"))
				{
					out.write("var "+ dot_var + " : int;");
					out.newLine();
				}
				else if (type.equals("boolean"))
				{
					out.write("var "+ dot_var + " : bool;");
					out.newLine();
				}
				else if (type.equals("object") || type.equals("character"))
				{
					out.write("var "+ dot_var + " : T;");
					out.newLine();
				}
				out.newLine();	
			}
		}//end for


	}//end declare_vars(Document doc)	

	public static void get_types_of_objects(Document doc)
	{
		Element e1;
		NodeList type = doc.getElementsByTagName("type");
		int type_len = type.getLength();

		if(type_len > 0)
		{							
			for (int i=0; i < type_len; i++)
			{
				e1 = (Element)type.item(i);
				String val = e1.getAttributeNode("name").getValue();
				//System.out.println(val);

				if(val.equals("finiteset(object)"))
					set_object = 1;
				else if (val.equals("finiteset(integer)"))
					set_integer = 1;
				else if(val.equals("string(object)"))
					string_object = 1;
				else if (val.equals("string(integer)"))
					string_integer = 1;
			}
		}
	}

	public static void removeWhitespace(Node n) {
		NodeList nl = n.getChildNodes();
		for (int pos = 0, c = nl.getLength(); pos < c; pos++) {
			Node child = nl.item(pos);
			if (child.getNodeType() != Node.TEXT_NODE) {
				removeWhitespace(child);
			}
		}

		// count backwards so that pos is correct even if nodes are removed
		for (int pos = nl.getLength() - 1; pos >= 0; pos--) {
			Node child = nl.item(pos);
			if (child.getNodeType() == Node.TEXT_NODE) {
				// if node's text is made up only of whitespace characters
				if (child.getTextContent().trim().equals("")) {
					n.removeChild(child);
				}
			}
		}
	}

	public void traverseTree(Node node, Document doc) throws Exception
	{
		NodeList n1 = null;

		// Extract node info:
		String elementName = node.getNodeName();
	
		if(elementName.equals("neq"))
		{
			out.write("(");
			traverseTree(node.getFirstChild(), doc);
			out.write("!=");
			traverseTree(node.getLastChild(), doc);
			out.write(")");
		}

		else if(elementName.equals("eq"))
		{
			out.write("(");
			traverseTree(node.getFirstChild(), doc);
			out.write("==");
			traverseTree(node.getLastChild(), doc);
			out.write(")");

		}					 

		else if(elementName.equals("geq"))
		{
			out.write("(");
			traverseTree(node.getFirstChild(), doc);
			out.write(">=");
			traverseTree(node.getLastChild(), doc);
			out.write(")");
		}

		else if(elementName.equals("leq"))
		{
			out.write("(");
			traverseTree(node.getFirstChild(), doc);
			out.write("<=");
			traverseTree(node.getLastChild(), doc);
			out.write(")");
		}

		else if(elementName.equals("gt"))
		{
			out.write("(");
			traverseTree(node.getFirstChild(), doc);
			out.write(">");
			traverseTree(node.getLastChild(), doc);
			out.write(")");
		}

		else if(elementName.equals("lt"))
		{
			out.write("(");
			traverseTree(node.getFirstChild(), doc);
			out.write("<");
			traverseTree(node.getLastChild(), doc);
			out.write(")");
		}

		else if(elementName.equals("add")) // for integers
		{
			out.write("(");
			traverseTree(node.getFirstChild(), doc);
			out.write("+");
			traverseTree(node.getLastChild(), doc);
			out.write(")");
		}

		else if(elementName.equals("subtract")) // for integers
		{
			out.write("(");
			traverseTree(node.getFirstChild(), doc);
			out.write("-");
			traverseTree(node.getLastChild(), doc);
			out.write(")");
		}

		else if(elementName.equals("star")) // for integers
		{	
			out.write("(");
			traverseTree(node.getFirstChild(), doc);
			
			String type = node.getAttributes().getNamedItem("type").getNodeValue();
			if(type.equals("string(object)") ||type.equals("string(integer)") 
					||type.equals("string(character)"))
			{
				out.write("+");
			}
			else
				out.write("*");
			traverseTree(node.getLastChild(), doc);
			out.write(")");
		}

		/*OCT2013*/
		else if(elementName.equals("mod")) // for integers
		{
			out.write("(");
			traverseTree(node.getFirstChild(), doc);
			out.write("%");
			traverseTree(node.getLastChild(), doc);
			out.write(")");
		}
		else if(elementName.equals("union"))
		{
			out.write("(");
			traverseTree(node.getFirstChild(), doc);
			out.write("+");
			traverseTree(node.getLastChild(), doc);
			out.write(")");
		}

		else if(elementName.equals("intersection"))
		{
			out.write("(");
			traverseTree(node.getFirstChild(), doc);
			out.write("*");
			traverseTree(node.getLastChild(), doc);
			out.write(")");
		}
		else if(elementName.equals("and"))
		{
			out.write("(");
			traverseTree(node.getFirstChild(), doc);			
			out.write(" && ");
			traverseTree(node.getLastChild(), doc);
			out.write(")");
		}

		else if(elementName.equals("or"))
		{
			out.write("(");
			traverseTree(node.getFirstChild(), doc);
			out.write(" || ");
			traverseTree(node.getLastChild(), doc);
			out.write(")");
		}
		else if(elementName.equals("implies"))
		{
			out.write("(");
			traverseTree(node.getFirstChild(), doc);
			out.write(" ==> ");
			traverseTree(node.getLastChild(), doc);
			out.write(")");
		}
		else if(elementName.equals("iff"))
		{
			out.write("(");
			traverseTree(node.getFirstChild(), doc);
			out.write(" <==> ");
			traverseTree(node.getLastChild(), doc);
			out.write(")");
		}

		else if(elementName.equals("bar"))
		{

			String type = node.getFirstChild().getAttributes().getNamedItem("type").getNodeValue();			

			if(type.equals("string(object)") || type.equals("string(integer)") || type.equals("string(character)"))
			{
				out.write("(|");
				traverseTree(node.getFirstChild(), doc);
				out.write("|) ");
			}

			else if(type.equals("finiteset(object)"))//|| type.equals("finiteset(tuple(d:object,r:object))")
			{
				out.write("(cardinality (");
				traverseTree(node.getFirstChild(), doc);
				out.write(")) ");				
			}
			else if(type.equals("integer"))
			{
				out.write("(absoluteValue (");
				traverseTree(node.getFirstChild(), doc);
				out.write(")) ");				
			}
		}

		else if (elementName.equals("dot"))
		{
			String p1 = node.getFirstChild().getTextContent();
			String p2 =node.getLastChild().getTextContent();
			String dot_var = p1+"_"+p2;
			if (dot_var.contains("."))
			{
				int index = dot_var.indexOf(".");	                
				dot_var = dot_var.substring(0, index) + "_" + dot_var.substring(index + 1);
			}
			out.write(" " +dot_var + " ");
		}
		else if(elementName.equals("negate"))
		{
			out.write("(- ");
			traverseTree(node.getFirstChild(), doc);
			out.write(") ");
		}
		else if(elementName.equals("difference"))
		{
			out.write("( ");
			traverseTree(node.getFirstChild(), doc);
			out.write("-");
			traverseTree(node.getLastChild(), doc);
			out.write(") ");
		}

		else if(elementName.equals("singleton"))
		{
			out.write("({ ");
			traverseTree(node.getFirstChild(), doc);
			out.write("}) ");
		}
		else if(elementName.equals("stringleton"))
		{
			out.write("([ ");
			traverseTree(node.getFirstChild(), doc);
			out.write("]) ");
		}
		else if(elementName.equals("symbol") && !(node.getParentNode().getNodeName().toString().equals("dot")))
		{
			String symbol = node.getFirstChild().getTextContent();
			if (symbol.contains("."))
			{
				int index = symbol.indexOf(".");	                
				symbol = symbol.substring(0, index) + "_" + symbol.substring(index + 1);
				//System.out.println(symbol);
			}
			out.write(" " +symbol + " ");

		}

		else if(elementName.equals("constant"))
		{
			//op = read_text_set(node);
			String constant = node.getFirstChild().getTextContent();			
			out.write(" " +constant + " ");			
		}

		else if(elementName.equals("emptyset"))
		{
			out.write(" {}");			
		}
		else if(elementName.equals("emptystring"))
		{
			out.write(" []");
		}
		else if(elementName.equals("stringleton"))
		{
			out.write("([ ");
			traverseTree(node.getFirstChild(), doc);
			out.write("]) ");
		}
		else if(elementName.equals("zero"))
		{
			out.write(" 0");
		}

		else if(elementName.equals("is_initial"))
		{

			out.write(" (is_initial (");
			traverseTree(node.getFirstChild(), doc);
			out.write(")) ");
		}
		else if(elementName.equals("elements"))
		{

			out.write(" (elements (");
			traverseTree(node.getFirstChild(), doc);
			out.write(")) ");
		}

		else if(elementName.equals("element"))
		{
			out.write(" ( ");
			traverseTree(node.getFirstChild(), doc);
			out.write("in");
			traverseTree(node.getLastChild(), doc);

			out.write(") ");
		}

		else if(elementName.equals("not"))
		{

			out.write("( ! ");
			traverseTree(node.getFirstChild(), doc);
			out.write(")  ");
		}

		else if(elementName.equals("thereexists") || elementName.equals("exists"))
		{
			out.write("(exists ");
			n1 = node.getChildNodes();
			for(int a= 0; a < n1.getLength()-1; a++)
			{
				traverseTree(n1.item(a), doc);
				if(a < n1.getLength()-2)
					out.write(", ");
			}
			out.write(":: ");
			traverseTree(node.getLastChild(), doc);
			out.write(")");
		}

		else if(elementName.equals("forall"))
		{
			out.write("(forall ");

			n1 = node.getChildNodes();
			for(int a= 0; a < n1.getLength()-1; a++)
			{
				traverseTree(n1.item(a), doc);
				if(a < n1.getLength()-2)
					out.write(", ");
			}
			out.write(":: ");
			traverseTree(node.getLastChild(), doc);
			out.write(")");
		}

		else if(elementName.equals("vars"))
		{
			String type = node.getAttributes().getNamedItem("type").getNodeValue();
			String dfny_type= "";

			//check whether the symbol has been declared or not

			if(type.equals("finiteset(object)"))
			{

				dfny_type = "set<T>";
			}

			if(type.equals("string(object)") || type.equals("string of item") 
					|| type.equals("string") || type.equals("string(character)"))
			{

				dfny_type = "seq<T>";
			}

			if(type.equals("string(integer)") )
			{

				dfny_type = "seq<int>";
			}

			else if (type.equals("object"))
			{
				dfny_type = "T";
			}

			else if (type.equals("integer"))
			{
				dfny_type = "int" ;
			}
//			else
//			{
//				dfny_type = "gahhh";
//			}

			NodeList var = node.getChildNodes();
			int v = var.getLength();
			
			/*//if there are multiple variables, we need to add commas between their names
			if(v>1)
			{
				for (int j =0; j<v-1; j++)
				{
					String vars = var.item(j).getTextContent();
					out.write(vars + ",");
				}
			}
			String vars = var.item(v-1).getTextContent();

			out.write(vars + " ");
			out.write(":"+dfny_type);*/
			
			//will not put commas between vars- instead will declare type multiple times
			
			if(v>1)
			{
				for (int j =0; j<v-1; j++)
				{
					String vars = var.item(j).getTextContent();
					out.write(vars);
					out.write(" :"+dfny_type);
					out.write(", ");
				}
			}
			String vars = var.item(v-1).getTextContent();
			out.write(vars);
			out.write(" :"+dfny_type+" ");
			
		}//end else if(elementName.equals("vars"))
			
			

		else if(elementName.equals("body"))
		{
			//System.out.println("found body");
			traverseTree(node.getFirstChild(), doc);

		}
		else if(elementName.equals("true"))
		{
			out.write("true");
		}
		else if(elementName.equals("false"))
		{
			out.write("false");
		}

		else if(elementName.equals("function"))
		{
			String name = node.getAttributes().getNamedItem("name").getNodeValue();

			out.write(" "+name+ "(");

			NodeList args = node.getChildNodes();
			int a = args.getLength();

			//findMethods(doc);

			if (a> 1) 
			{
				for (int j = 0; j < a-1; j++)
				{
					traverseTree(args.item(j).getFirstChild(), doc);
					out.write(",");
				}
			}
			traverseTree(args.item(a-1).getFirstChild(), doc);
			out.write(")  ");
		}
		else if(elementName.equals("substring") || elementName.equals("SUBSTRING"))
		{
			out.write("substring( ");
			traverseTree(node.getFirstChild(), doc);
			out.write(",");
			traverseTree(node.getFirstChild().getNextSibling(), doc);
			out.write(",");
			traverseTree(node.getLastChild(), doc);
			out.write(")");
		}
		else if(elementName.equals("reverse"))
		{
			out.write("reverse( ");
			traverseTree(node.getFirstChild(), doc);
			out.write(")");
		}

	}//end traverseTree(Node node)

	public void declare_funs_dynamic(Document doc) throws IOException
	{
		//find the in-built symbols and declare their corresponding functions
		declare_inbuilt_funs(doc);

		NodeList restricted_funs = doc.getElementsByTagName("restricted");
		expand_restrictions(doc, restricted_funs);

		NodeList impl_funs = doc.getElementsByTagName("implicit");
		expand_fun(doc, impl_funs, false);

		NodeList expl_funs = doc.getElementsByTagName("explicit");
		expand_fun(doc, expl_funs, true );

	}

	public void declare_inbuilt_funs( Document doc) throws IOException
	{
		Element e1 ; 

		//find is_initial
		NodeList is_initial = doc.getElementsByTagName("is_initial");
		if(is_initial.getLength() > 0)
		{
			out.newLine();	
			out.write("function is_initial(x: T) : bool");
			out.newLine();

		}

		NodeList substring = doc.getElementsByTagName("substring");
		int substring_len = substring.getLength();

		if(substring_len > 0)
		{
			for (int i=0; i < substring_len; i++)
			{
				e1 = (Element)substring.item(i);

				String val = e1.getAttributeNode("type").getValue();
				//System.out.println(val);

				if(val.equals("string(object)"))
				{
					out.newLine();	
					out.write("function substring(s: seq<T>, start : int, finish: int) : seq<T>");
					out.newLine();
					break;
				}
				else if(val.equals("string(integer)"))
				{
					out.newLine();	
					out.write("function substring(s: seq<int>, start : int, finish: int) : seq<int>");
					out.newLine();	
					break;
				}
			}			
		}

		NodeList reverse = doc.getElementsByTagName("reverse");
		int reverse_len = reverse.getLength();

		if(reverse_len > 0)
		{							
			for (int i=0; i < reverse_len; i++)
			{
				e1 = (Element)reverse.item(i);

				String val = e1.getAttributeNode("type").getValue();
				//System.out.println(val);

				if(val.equals("string(object)"))
				{
					out.newLine();	
					out.write("function reverse(s: seq<T>): seq<T> ");
					out.newLine();
					break;
				}
				else if(val.equals("string(integer)"))
				{
					out.newLine();	
					out.write("function reverse(s: seq<int>): seq<int> ");
					out.newLine();	
					break;
				}
			}			
		}//endif(reverse_len > 0)

		NodeList elements = doc.getElementsByTagName("elements");
		int elements_len = elements.getLength();

		if(elements_len > 0)
		{							
			for (int i=0; i < elements_len; i++)
			{
				e1 = (Element)elements.item(i);
				//System.out.print(e1.getTagName() + ":");

				String val = e1.getAttributeNode("type").getValue();
				//System.out.println(val);

				if(val.equals("finiteset(object)"))
				{
					out.newLine();	
					out.write("function elements(s: seq<T>): set<T>");
					out.newLine();
					break;
				}
				else if(val.equals("finiteset(integer)"))
				{
					out.newLine();	
					out.write("function elements(s: seq<int>): set<int>");
					out.newLine();	
					break;
				}
			}			
		}//endif(elements_len > 0)

		NodeList bar = doc.getElementsByTagName("bar");		
		int bar_len = bar.getLength();
		//System.out.println(bar_len);

		//need to determine bar for set(object) or set(integer) 
		if(bar_len > 0)
		{							
			for (int i=0; i < bar_len; i++)
			{
				e1 = (Element)bar.item(i);
				if(set_object == 1)
				{
					out.newLine();	
					out.write("function cardinality (s: set<T>) :int");
					out.newLine();	
					break;
				}
				else if (set_integer == 1)
				{
					out.newLine();	
					out.write("function cardinality (s: set<int>) :int");
					out.newLine();	
					break;
				}
				else 
				{
					out.newLine();
					out.write("function absoluteValue (x: int) :int");
					out.newLine();
					out.write("{ if (x >= 0) then x else  -x }");
					out.newLine();
					break;
				}
			}			
		}//if(bar_len > 0)
	}

	public void expand_restrictions(Document doc, NodeList funs) throws IOException
	{
		Element e1 ;
		Node n1;
		NamedNodeMap nnm1;

		String attrname;
		String attrval;
		int len; boolean decld = false;

		len = funs.getLength();
		//System.out.println("len is :"+len);

		for (int i=0; i < len; i++)
		{
			e1 = (Element)funs.item(i);

			//trying to get the params
			NodeList params =  e1.getFirstChild().getChildNodes();
			int p = params.getLength();
			//if there are any parameters
			if(p !=0)
			{
				nnm1 = e1.getAttributes();

				if (nnm1 != null)
				{
					for (int j=0; j < nnm1.getLength(); j++)
					{
						n1 = nnm1.item(j);
						attrname = n1.getNodeName(); //name
						attrval = n1.getNodeValue(); //MOD
						//System.out.print(" " + attrname + " = " + attrval);
						
						
						if(!fun_decld.contains(attrval))							
						{
						fun_decld.add(attrval);
						out.write("function "+attrval+" (");
						decld = true;
						
						}
					}
				}

				//get params and return val
				if(decld == true)
				{
				get_Params(doc, e1);
				out.newLine();
				}
				
				//resetting for the next function
				decld = false;
			}//if(p !=0)		

		}
	}

	public void expand_fun(Document doc, NodeList funs, boolean is_explicit) throws IOException
	{
		Element e1 ;
		Node n1;
		NamedNodeMap nnm1;

		String attrname;
		String attrval;
		int len; boolean decld = false;

		len = funs.getLength();
		//System.out.println("len is :"+len);

		for (int i=0; i < len; i++)
		{
			e1 = (Element)funs.item(i);
			//System.out.println(e1.getTagName() + ":"); //implicit
			nnm1 = e1.getAttributes();

			if (nnm1 != null)
			{
				for (int j=0; j < nnm1.getLength(); j++)
				{
					n1 = nnm1.item(j);
					attrname = n1.getNodeName(); //name
					attrval = n1.getNodeValue(); //MOD
					//System.out.print(" " + attrname + " = " + attrval);

					
					if(!fun_decld.contains(attrval))
					{
					fun_decld.add(attrval);
					out.write("function "+attrval+" (");
					decld = true;
					}
				}
			}
			//System.out.println();

			//get params and return val
			if(decld == true)
			{
			get_Params(doc, e1);
			out.newLine();
			}
			//resetting for the next function
			decld = false;
		}//end for i

	}

	//this method prints the params and returns the no. of params found
	public void get_Params(Document doc, Element e1) throws IOException
	{
		String attrval;		
		NamedNodeMap nnm3;
		Node n3;

		//trying to get the params
		NodeList params =  e1.getFirstChild().getChildNodes();
		
		get_Params_helper(doc, params);
		//out.write("**returned from helper**");
		out.write(")");

		//the return val		

		Node retval = e1.getFirstChild().getNextSibling();
		//System.out.println("retval.getNodeName() : "+retval.getAttributes());
		nnm3 = retval.getAttributes();

		if (nnm3 != null)
		{				
			n3 = nnm3.item(0);
			attrval = n3.getNodeValue();
			//System.out.println("attrval: "+attrval);

			if(attrval.equals("finiteset(object)"))
			{

				out.write(": set<T>");
			}

			else if(attrval.equals("finiteset(integer)"))
			{

				out.write(" : set<int>");
			}

			else if (attrval.equals("object") || attrval.equals("character"))
			{
				out.write(" : T");
			}

			else if (attrval.equals("integer"))
			{
				out.write(" : int");
			}
			else if (attrval.equals("boolean"))
			{
				out.write(" : bool");
			}
			else if (attrval.equals("string(object)") || attrval.equals("string(character)"))
			{
				out.write(" : seq<T>");
			}
			else if (attrval.equals("string(integer)") )
			{
				out.write(" : seq<int>");
			}
			
		}
	}

	public void get_Params_helper(Document doc, NodeList params)  throws IOException
	{
		Element e2, e3;
		String attrname, attrval, attrname1, attrval1;
		NamedNodeMap nnm2,nnm3;
		Node n2, n3;

		int p = params.getLength();
		//System.out.println("params.getLength()"+params.getLength());
		if(p > 0)
		{
			//if there are multiple params, we need to add commas between their names
			if(p>1)
			{
				for (int k=0; k < p-1; k++)
				{
					e2 = (Element)params.item(k);
					//System.out.println(e2.getTagName() + ":");
					nnm2 = e2.getAttributes();

					if (nnm2 != null)
					{
						for (int a=0; a<nnm2.getLength(); a++)
						{
							n2 = nnm2.item(a);
							attrname = n2.getNodeName(); 
							attrval = n2.getNodeValue(); 
							//System.out.print(" " + attrname + " = " + attrval);

							if(attrval.equals("finiteset(object)"))
							{

								out.write(": set<T>, ");
							}

							else if(attrval.equals("finiteset(integer)"))
							{

								out.write(" : set<int>, ");
							}

							else if (attrval.equals("object") || attrval.equals("character"))
							{
								out.write(" : T, ");
							}

							else if (attrval.equals("integer"))
							{
								out.write(" : int, ");
							}
							else if (attrval.equals("string(object)")  || attrval.equals("string(character)"))
							{
								out.write(" : seq<T>, ");
							}
							else if (attrval.equals("string(integer)"))
							{
								out.write(" : seq<int>, ");
							}
						
							else
							{
								//prints the name of the param
								out.write(attrval+" ");
							}
						}
					}
					//System.out.println();
				}//end k
			}//end if(p>1)

			//the last param
			e3 = (Element)params.item(p-1);
			
			nnm3 = e3.getAttributes();
			//System.out.println(nnm3.getLength());

			if (nnm3 != null)
			{
				for (int z=0; z < nnm3.getLength(); z++)
				{
					//System.out.print("!!!!");
					n3 = nnm3.item(z);
					//System.out.print(n3.toString());
					attrname1 = n3.getNodeName(); 
					attrval1 = n3.getNodeValue(); 
					//System.out.println(" " + attrname1 + " = " + attrval1);

					if(attrval1.equals("finiteset(object)"))
					{

						out.write(": set<T>");
						//out.write("**printing the type**");
					}

					else if(attrval1.equals("finiteset(integer)"))
					{

						out.write(" : set<int>");
					}

					else if (attrval1.equals("object") || attrval1.equals("character"))
					{
						out.write(" : T");
					}

					else if (attrval1.equals("integer"))
					{
						out.write(" : int");
					}
					else if (attrval1.equals("string(object)") || attrval1.equals("string(character)"))
					{
						out.write(" : seq<T>");
					}
					else if (attrval1.equals("string(integer)"))
					{
						out.write(" : seq<int>");
					}
					
					else
					{
						//prints the name of the param
						out.write(attrval1+" ");
						//out.write("**printing the name**");
					}
				}
			}//end if (nnm3 != null)
		}
	}

	public void explicit_funs_body(Document doc) throws IOException
	{
		NodeList expl_funs = doc.getElementsByTagName("explicit");

		Element e1;	int len;
		String attrname, attrval;
		NamedNodeMap nnm1;
		Node n1;

		len = expl_funs.getLength();

		for (int i=0; i < len; i++)
		{
			e1 = (Element)expl_funs.item(i);

			//trying to get the params
			NodeList params =  e1.getFirstChild().getChildNodes();

			out.newLine();
			out.write("assume forall ");			

			//write the name of the function and the params
			get_Params_helper(doc, params);

			out.write (" ::");

			nnm1 = e1.getAttributes();

			if (nnm1 != null)
			{
				for (int j=0; j < nnm1.getLength(); j++)
				{
					n1 = nnm1.item(j);
					attrname = n1.getNodeName(); //name
					attrval = n1.getNodeValue(); //MOD
					//System.out.print(" " + attrname + " = " + attrval);

					fun_decld.add(attrval);
					out.write(" "+attrval+" (");
				}
			}

			//the function call

			Element e3;		

			int p = params.getLength();
			//System.out.println("params.getLength()"+params.getLength());
			if(p > 0)
			{
				//if there are multiple params, we need to add commas between their names
				if(p>1)
				{
					for (int k=0; k < p- 1; k++)
					{
						e3 = (Element)params.item(k);
						String name = e3.getAttributes().getNamedItem("name").getNodeValue();

						//prints the name of the param
						out.write(name+", ");

					}//end k
				}

				e3 = (Element)params.item(p-1);
				String name = e3.getAttributes().getNamedItem("name").getNodeValue();

				//prints the name of the param
				out.write(name+" ");
			}//if(p > 0)
		

		out.write(") == (");
		Node expr = e1.getLastChild();
		//System.out.println("expr.getNodeName() : "+expr.getNodeName());

		try {
			traverseTree(expr.getFirstChild(), doc);
		} catch (Exception e) {
			e.printStackTrace();
		}

		out.write(");");
		out.newLine();

	}//for (int i=0; i < len; i++)
}

public void implicit_funs_body(Document doc) throws IOException
{
	NodeList impl_funs = doc.getElementsByTagName("implicit");

	Element e1;

	int len;
	len = impl_funs.getLength();

	//System.out.println("len is :"+len);

	for (int i=0; i < len; i++)
	{
		e1 = (Element)impl_funs.item(i);

		out.newLine();
		out.write("assume ");

		Node expr = e1.getLastChild();
		//System.out.println("expr.getNodeName() : "+expr.getNodeName());

		try {
			traverseTree(expr.getFirstChild(), doc);
		} catch (Exception e) {			
			e.printStackTrace();
		}

		out.write(";");
		out.newLine();

	}//for (int i=0; i < len; i++)
}

public void restrictions_body(Document doc) throws IOException
{
	NodeList restricted_funs = doc.getElementsByTagName("restricted");		
	Element e1;		
	int len;
	len = restricted_funs.getLength();

	//System.out.println("len is :"+len);
	for (int i=0; i < len; i++)
	{
		e1 = (Element)restricted_funs.item(i);
		//System.out.println(e1.getNodeName());


		out.newLine();
		out.write("assume ");

		Node expr = e1.getLastChild();
		//System.out.println("expr.getFirstChild().getNodeName() : "+expr.getFirstChild().getNodeName());

		try {
			traverseTree(expr.getFirstChild(), doc);
		} catch (Exception e) {
			e.printStackTrace();
		}

		out.write(";");			
	}//for (int i=0; i < len; i++)
}

//	public void declare_funs(Document doc) throws IOException
//	{
//		NodeList substring = doc.getElementsByTagName("substring");
//
//		NodeList reverse = doc.getElementsByTagName("reverse");
//
//		String cName = doc.getDocumentElement().getAttribute("cName");
//
//		/*OCT2013*/
//		//out.write("function MOD (i: int, j:int ):int");
//		//out.newLine();
//		//out.write("function REM (i: int, j:int ):int");
//
//		//find is_initial
//
//		NodeList is_initial = doc.getElementsByTagName("is_initial");
//
//		if(is_initial.getLength() > 0)
//		{
//			out.newLine();	
//			out.write("function is_initial(x: T) : bool");
//			out.newLine();
//			//	out.write("{}");
//			out.newLine();
//		}
//		NodeList elements = doc.getElementsByTagName("elements");
//
//		if(cName.contains("ListOfIntegerFacility"))
//		{
//			if(elements.getLength() > 0)
//			{
//				out.newLine();	
//				out.write(" function elements(s: seq<int>): set<int>");
//				out.newLine();
//				out.newLine();
//			}
//		}
//		else
//		{
//
//			if(elements.getLength() > 0)
//			{
//				out.newLine();	
//				out.write(" function elements(s: seq<T>): set<T>");
//				out.newLine();
//				out.newLine();
//			}
//
//		}
//		//List definitions
//
//		if(cName.contains("Natural"))
//		{
//			if(reverse.getLength() > 0)
//			{
//				out.newLine();	
//				out.write("function reverse(s: seq<int>): seq<int> ");
//				out.newLine();
//				out.newLine();
//			}
//
//		}
//		else
//		{
//			if(reverse.getLength() > 0)
//			{
//				out.newLine();	
//				out.write("function reverse(s: seq<T>): seq<T> ");
//				out.newLine();
//				out.newLine();
//			}
//		}//end else
//
//		NodeList fn = doc.getElementsByTagName("function");
//
//		int numfuns = fn.getLength();
//		out.newLine();	
//
//		for (int i = 0; i < numfuns; i++) 
//		{
//			//System.out.println(vars.item(i).getFirstChild().toString()); 
//			String fn_name = fn.item(i).getAttributes().getNamedItem("name").getNodeValue();
//
//			//System.out.println(fn_name);
//			if (!(var_decld.contains(fn_name)))
//			{
//				var_decld.add(fn_name);
//
//				if(cName.contains("QueueOfIntegerFacility"))
//				{
//					if(fn_name.equals("OCCURS_COUNT"))
//					{
//
//						out.write("function "+ fn_name + " (s : seq<int>, i :int): int");
//						out.newLine();
//					}
//					else if(fn_name.equals("ARE_PERMUTATIONS"))
//					{
//
//						out.write("function "+ fn_name + " (s1 :seq<int>, s2: seq<int>): bool");
//						out.newLine();
//					}
//					else if(fn_name.equals("PRECEDES"))
//					{
//
//						out.write("function "+ fn_name + "  (s1: seq<int>, s2: seq<int>): bool");
//						out.newLine();
//					}
//					else if(fn_name.equals("IS_NONDECREASING"))
//					{
//
//						out.write("function "+ fn_name + " (s: seq<int>): bool ");
//						out.newLine();
//					}
//
//				}//end if
//				else
//				{
//					if(fn_name.equals("ARE_IN_ORDER"))
//					{
//
//						out.write("function "+ fn_name + " (x : T, y : T) : bool");
//						out.newLine();
//					}
//
//					else if(fn_name.equals("OCCURS_COUNT"))
//					{
//
//						out.write("function "+ fn_name + " (s : seq<T>, i :T): int");
//						out.newLine();
//					}
//					else if(fn_name.equals("ARE_PERMUTATIONS"))
//					{
//
//						out.write("function "+ fn_name + " (s1 :seq<T>, s2: seq<T>): bool");
//						out.newLine();
//					}
//					else if(fn_name.equals("PRECEDES"))
//					{
//
//						out.write("function "+ fn_name + "  (s1: seq<T>, s2: seq<T>): bool");
//						out.newLine();
//					}
//					else if(fn_name.equals("IS_NONDECREASING"))
//					{
//
//						out.write("function "+ fn_name + " (s: seq<T>): bool ");
//						out.newLine();
//					}
//				}//end else
//
//				if(fn_name.equals("IS_PRECEDING"))
//				{
//
//					out.write("function "+ fn_name + " (x: set<T>, y: set<T>) : bool ");
//					out.newLine();
//				}
//				else if(fn_name.equals("IS_ODD"))
//				{
//
//					out.write("function "+ fn_name + " (n: int): bool ");
//					out.newLine();
//				}
//				else if(fn_name.equals("DIFFER_BY_ONE"))
//				{
//
//					out.write("function "+ fn_name + " (t1: seq<T>, t2: seq<T>, pos: int, ch: T): bool ");
//					out.newLine();
//				}
//				else if(fn_name.equals("SAME_EXCEPT_AT"))
//				{
//
//					out.write("function "+ fn_name + " (t1: seq<T>, t2: seq<T>, pos: int, x: T, y: T): bool ");
//					out.newLine();
//				}
//				else if(fn_name.equals("SUBSTRING"))
//				{
//
//					out.write("function "+ fn_name + " (s: seq<T>, start : int, finish: int) : seq<T>");
//					out.newLine();
//				}
//				else if(fn_name.equals("SUBSTRING_REPLACEMENT"))
//				{
//
//					out.write("function "+ fn_name + " (s: seq<T>, ss: seq<T>, start: int, finish: int): seq<T>");
//					out.newLine();
//				}
//				else if(fn_name.equals("FUNCTION"))
//				{
//
//					out.write("function "+ fn_name + " (x: set<T>): set<T>");
//					out.newLine();
//				}
//				else if(fn_name.equals("HAS_ONLY_DIGITS"))
//				{
//
//					out.write("function "+ fn_name + " (digits: seq<int>, radix: int): bool");
//					out.newLine();
//				}
//				else if(fn_name.equals("NUMERICAL_VALUE"))
//				{
//
//					out.write("function "+ fn_name + " (s: seq<int>, r: int): int");
//					out.newLine();
//				}
//				else if(fn_name.equals("IS_WELL_FORMED_FUNCTION"))
//				{
//
//					out.write("function "+ fn_name + " (digits: seq<int>, radix: int): bool");
//					out.newLine();
//				}
//			}//end if
//		}//end for
//		out.newLine();	
//	}

public void declare_inbuiltfuns_and_lemmas(Document doc) throws IOException
{
	Element e1 ;
	NodeList substring = doc.getElementsByTagName("substring");
	int substring_len = substring.getLength();

	if(substring_len > 0)
	{	
		for (int i=0; i < substring_len; i++)
		{
			e1 = (Element)substring.item(i);
			String val = e1.getAttributeNode("type").getValue();

			if(val.equals("string(object)"))
			{
				out.newLine();	
				out.write("//substring definition");
				out.newLine();	
				out.write("assume ( forall s: seq<T>, start : int, finish: int ::(start < 0 || start > finish || finish > |s| ==> substring(s, start, finish) == []) && (!(start < 0 || start > finish || finish > |s|) ==> (exists a:seq<T>, b:seq<T> :: s == a + substring(s, start, finish) + b && |a| == start&& |b| == |s| - finish)));");
				out.newLine();
				/*out.write("//substring lemmas");
					out.newLine();	
					out.write("assume (forall s: seq<T>, start: int, finish: int :: start < 0 || start > finish || finish > |s| ==> substring(s, start, finish) == []);");
					out.newLine();
					out.write("assume (forall s: seq<T>, start: int, finish: int :: |s| == 0 ==> substring(s, start, finish) == []);");
					out.newLine();
					out.write("assume (forall m: int, n: int, a: seq<T> :: 0 <= m && m <= n && n <= |a| ==> substring(a, 0, m) + substring(a, m, n) == substring(a, 0, n));");
					out.newLine();
					out.write("assume (forall m: int, n: int, a: seq<T> :: 0 <= m && m <= n && n <= |a| ==> substring(a, 0, m) + substring(a, m, n) + substring(a, n, |a|) == a);");
					out.newLine();
					out.write("assume (forall j: int, k: int, s1: seq<T>, s2: seq<T> :: 0 <= j && j <= k && k <= |s1| ==> substring(s1 + s2, j, k) == substring(s1, j, k));");
					out.newLine();
					out.write("assume (forall j: int, k: int, s1: seq<T>, s2: seq<T> :: |s1| <= j && j <= k && k <= (|s1| + |s2|) ==> substring(s1 + s2, j, k) == substring(s2, j - |s1|, k - |s1|));");
					out.newLine();*/
				out.newLine();
				break;
			}
			else if(val.equals("string(integer)"))
			{
				out.newLine();	
				out.write("//substring definition");
				out.newLine();
				out.write("assume ( forall s: seq<int>, start : int, finish: int ::(start < 0 || start > finish || finish > |s| ==> substring(s, start, finish) == []) && (!(start < 0 || start > finish || finish > |s|) ==> (exists a:seq<int>, b:seq<int> :: s == a + substring(s, start, finish) + b && |a| == start&& |b| == |s| - finish)));");
				out.newLine();	
				/*out.write("//substring lemmas");
					out.newLine();
					out.write("assume (forall s: seq<int>, start : int, finish: int :: start < 0 || start > finish || finish > |s| ==> substring(s, start, finish) == []) ;");
					out.newLine();	
					out.write("assume (forall s: seq<int>, start : int, finish: int :: |s| == 0 ==> substring(s, start, finish) == []) ;");
					out.newLine();	
					out.write("assume (forall m: int, n:int, a: seq<int> ::  m >=0 && m <= n && n <= |a| ==> substring(a, 0, m) + substring(a, m, n) == substring(a, 0, n));"); 
					out.newLine();	
					out.write("assume (forall m: int, n:int, a: seq<int> :: m >=0 && m <= n && n <= |a| ==> substring(a, 0, m) + substring(a, m, n) + substring(a, n, |a|) == a );");
					out.newLine();	
					out.write("assume (forall j: int, k:int, s1: seq<int>, s2: seq<int> :: j >=0 && j <= k && k <= |s1| ==> substring(s1 + s2, j, k) == substring(s1, j, k));");
					out.newLine();	
					out.write("assume (forall j: int, k:int, s1: seq<int>, s2: seq<int> :: j >= |s1| && j <= k && k <= (|s1| + |s2|) ==> substring(s1 + s2, j, k) == substring(s2, j - |s1|, k - |s1|));");
					out.newLine();	*/
				out.newLine();		
				break;
			}
		}		
	}//end 	if(substring_len > 0)


	NodeList reverse = doc.getElementsByTagName("reverse");
	int reverse_len = reverse.getLength();

	if(reverse_len > 0)
	{	
		for (int i=0; i < reverse_len; i++)
		{
			e1 = (Element)reverse.item(i);
			String val = e1.getAttributeNode("type").getValue();

			if(val.equals("string(object)"))
			{
				out.newLine();	
				out.write("//reverse definition");
				out.newLine();
				out.write("assume (forall s:seq<T> :: if s ==[] then reverse(s) == [] else (exists t: seq<T>, x: T :: s == [x] + t && reverse(s) == reverse(t) + [x]));");
				out.newLine();	
				/*out.write("//reverse lemmas");
					out.newLine();
					out.write("assume (reverse([]) == []);");
					out.newLine();
					out.write("assume (forall x: T :: reverse([x]) == [x]);");
					out.newLine();
					out.write("assume (forall s1: seq<T>, s2: seq<T> :: s1 == reverse(s2) ==> s2 == reverse(s1));");
					out.newLine();
					out.write("assume (forall s1: seq<T>, s2: seq<T> :: reverse(s2 + s1) == reverse(s1) + reverse(s2));");
					out.newLine();
					out.write("assume (forall s1: seq<T>, s2: seq<T>, s3: seq<T>, s4: seq<T> :: ((reverse(s1) + s2) == (reverse(s3) + s4) && |s3| == |s1|)==> (s1 == s3 && s2 == s4));");
					out.newLine();
					out.write("assume (forall s1: seq<T> :: |reverse(s1)| == |s1|);");
					out.newLine();
					out.write("assume (forall s1: seq<T>, s2: seq<T> :: (reverse(s1) == reverse(s2)) ==> (s1 == s2));");
					out.newLine();*/
				out.newLine();
				break;
			}
			else if(val.equals("string(integer)"))
			{
				out.newLine();	
				out.write("//reverse definition");
				out.newLine();
				out.write("assume (forall s:seq<int> :: if s ==[] then reverse(s) == [] else (exists t: seq<int>, x: int :: s == [x] + t && reverse(s) == reverse(t) + [x]));");
				out.newLine();	
				/*out.write("//reverse lemmas");
					out.newLine();
					out.write("assume (forall s1:seq<int>, s2:seq<int> :: s1 == reverse(s2) ==> s2 == reverse(s1));");
					out.newLine();
					out.write("assume (reverse([]) == []);");
					out.newLine();
					out.write("assume(forall x: int :: reverse([x]) == [x]);");
					out.newLine();
					out.write("assume (forall x: seq<int>, s: seq<int> :: reverse(s + x) == reverse(x) + reverse(s));");
					out.newLine();
					out.write("assume ( forall s1:seq<int>, s2: seq<int>, s3: seq<int>, s4: seq<int> :: ((reverse(s1) + s2) == (reverse(s3) + s4) && |s3| == |s1| )==> (s1 ==s3 && s2 == s4));");
					out.newLine();
					out.write("assume (forall a: seq<int> :: |reverse(a)| == |a|);");
					out.newLine();
					out.write("assume (forall a: seq<int>, b: seq<int> :: (reverse(a) == reverse(b)) ==> (a == b));");
					out.newLine();*/
				out.newLine();
				break;
			}
		}		
	}//endif(reverse_len > 0)

	NodeList elements = doc.getElementsByTagName("elements");
	int elements_len = elements.getLength();

	if(elements_len > 0)
	{							
		for (int i=0; i < elements_len; i++)
		{
			e1 = (Element)elements.item(i);						
			String val = e1.getAttributeNode("type").getValue();

			if(val.equals("finiteset(object)"))
			{
				out.newLine();	
				out.write("// elements definition");
				out.newLine();
				out.write("assume (forall s:seq<T> :: if s ==[] then elements(s) == {} else (exists t: seq<T>, x: T :: s == [x] + t && elements(s) == {x} + elements(t)));");
				out.newLine();	
				/*out.write("//elements lemmas");
					out.newLine();
					out.write("assume(forall a:seq<T>, b: seq<T> :: elements(a+b) == elements(a) + elements(b));");
					out.newLine();
					out.write("assume(forall a:seq<T>, x: T :: elements([x] + a) == elements(a) + {x});");
					out.newLine();
					out.write("assume(forall a:seq<T>, b:seq<T> :: (a == b) ==> (elements(a) == elements(b)));");
					out.newLine();
					out.write("assume (forall a:seq<T>, b: seq<T>, c: seq<T> :: elements((a + (b + c))) == elements(((a + b) + c)));");
					out.newLine();
					out.write("assume (elements([]) == {});");
					out.newLine();
					out.write("assume (forall a: seq<T>, x: T :: ((elements([x] + a)) - {x}) == elements(a));");
					out.newLine();
					out.write("assume (forall a:seq<T>, b: seq<T>, x: T :: elements((a + b)) == (elements(((a + [x]) + b)) - {x}));");
					out.newLine();
					out.write("assume (forall a:seq<T>, b: seq<T>, c: seq<T> :: elements((a + b)) == (elements(((a + c) + b)) - elements(c)));");
					out.newLine();
					//out.write("assume (forall a: seq<T>, x: T :: (x !in elements(a)) ==> (|a + [x]| ) >= card(elements(a) + {x}));");
					//out.newLine();
					//out.write("assume (forall a: seq<T>, x: T :: (x !in elements(a)) ==>(card(elements(a)) < card(elements(a) + {x})));");
					//out.newLine();
					//out.write("assume(forall a: seq<T>, x: T :: |a+[x]| == card(elements(a)) + 1 ==> |a| == card(elements(a)));");
					//out.newLine();
					out.write("assume(forall a:seq<T>, b: seq<T> :: elements(a+b) == elements(b+a));");
					out.newLine();
					out.write("assume (forall a:seq<T>, b: seq<T>, c: seq<T> :: elements(((a + b) + c)) == elements(((c + b) + a)));");
					out.newLine();*/
				out.newLine();
				break;
			}
			else if(val.equals("finiteset(integer)"))
			{
				out.newLine();	
				out.write("assume (forall s:seq<int> :: if s ==[] then elements(s) == {} else (exists t: seq<int>, x: int :: s == [x] + t && elements(s) == {x} + elements(t)));");
				out.newLine();
				break;
			}
		}			
	}//endif(elements_len > 0)

	NodeList bar = doc.getElementsByTagName("bar");
	int bar_len = bar.getLength();

	//need to determine bar for set(object) or set(integer) 
	if(bar_len > 0)
	{							
		for (int i=0; i < bar_len; i++)
		{
			e1 = (Element)bar.item(i);
			if(set_object == 1)
			{
				out.newLine();	
				out.write("//cardinality lemmas		");	
				out.newLine();	
				out.write("assume (forall s: set<T> :: cardinality(s) >= 0);");
				out.newLine();	
				out.write("assume (forall s: set<T> :: s == {} ==> cardinality(s) == 0);");
				out.newLine();	
				out.write("assume (forall s: set<T>, x: T :: x in s ==> cardinality(s-{x}) == (cardinality(s) - 1 ));");
				out.newLine();	
				out.newLine();		
				break;
			}
			else if (set_integer == 1)
			{
				out.newLine();	
				out.newLine();	
				out.write("//cardinality lemmas		");	
				out.newLine();	
				out.write("assume (forall s: set<int> :: cardinality(s) >= 0);");
				out.newLine();	
				out.write("assume (forall s: set<int> :: s == {} ==> cardinality(s) == 0);");
				out.newLine();	
				out.write("assume (forall s: set<int>, x: int :: x in s ==> cardinality(s-{x}) == (cardinality(s) - 1 ));");
				out.newLine();	
				out.newLine();	
				out.newLine();	
				break;
			}
		}			
	}//if(bar_len > 0)

	/*
	 * 
	 * 
		if(cname.contains("QueueOfIntegerFacility"))
		{
			if(var_decld.contains("OCCURS_COUNT"))
			{
				out.newLine();	
				out.write("//definition of OCCURS_COUNT");
				out.newLine();
				out.write("assume ( forall s:seq<int>, i :int :: if s == [] then OCCURS_COUNT(s, i) == 0 else (exists x: int, r: seq<int> :: s == [x] + r && (if x == i then OCCURS_COUNT(s, i) == OCCURS_COUNT(r, i) +1 else OCCURS_COUNT(s, i) == OCCURS_COUNT(r, i)))); ");		
				out.newLine();
			}
			if(var_decld.contains("PRECEDES"))
			{
				out.newLine();	
				out.write("//definition of PRECEDES");
				out.newLine();
				out.write("assume (forall s1: seq<int>, s2: seq<int> :: PRECEDES(s1, s2) ==(forall i : int , j : int :: OCCURS_COUNT(s1, i) > 0 && OCCURS_COUNT(s2, j) > 0 ==> (i <= j))) ;");		
				out.newLine();
			}
			if(var_decld.contains("IS_NONDECREASING"))
			{
				out.newLine();	
				out.write("//definition of IS_NONDECREASING");
				out.newLine();
				out.write("assume (forall s: seq<int>:: IS_NONDECREASING(s) == (forall a: seq<int> , b: seq<int> :: s == a + b ==> PRECEDES(a, b)));  ");		
				out.newLine();
				out.write("//IS_NONDECREASING lemmas");
				out.newLine();
				out.write("assume (IS_NONDECREASING([]));");
				out.newLine();
				out.write("assume (forall x:int :: IS_NONDECREASING([x]));");
				out.newLine();
				out.write("assume (forall q: seq<int> :: |q| <= 1 ==> IS_NONDECREASING(q));");
				out.newLine();
				out.write("assume (forall x:seq<int> :: IS_NONDECREASING([]+x) ==> IS_NONDECREASING(x));");
				out.newLine();
				out.write("assume (forall x:seq<int> :: IS_NONDECREASING(x+[])  ==> IS_NONDECREASING(x));");
				out.newLine();
				out.write("assume (forall a: int, b: int :: (a <= b) ==> IS_NONDECREASING([a] + [b]));"); 
				out.newLine();
				out.write("assume (forall x: seq<int>, y: seq<int> :: IS_NONDECREASING(x+y) ==> IS_NONDECREASING(x) && IS_NONDECREASING (y));"); 
				out.newLine();
				out.write("assume (forall x: seq<int>, y: seq<int>, z: seq<int> :: IS_NONDECREASING(x+y+z) ==> IS_NONDECREASING(x + z) && IS_NONDECREASING(y + z) && IS_NONDECREASING(x + y));"); 
				out.newLine();
				out.write("assume(forall a: seq<int>, b:seq<int>, x: int, y:int :: IS_NONDECREASING(a + [y]) && IS_NONDECREASING([y] + b) ==> IS_NONDECREASING(a + [y] + b));");
				out.newLine();
				out.write("assume (forall a:seq<int>, b: seq<int>, x:int, y:int :: IS_NONDECREASING(a + [x]) && IS_NONDECREASING([y] + b) && (x <= y) ==> IS_NONDECREASING(a + [x] + [y] + b));");
				out.newLine();
				out.write("assume (forall a:seq<int>, b: seq<int>, x:int, y:int :: IS_NONDECREASING(a + [x]) && IS_NONDECREASING([y] + b) && (x <= y) ==> IS_NONDECREASING(a + ([x] + ([y] + b))));");
				out.newLine();
				out.write("assume (forall a:seq<int>, b: seq<int>, x:int, y:int :: IS_NONDECREASING(a + [x]) && IS_NONDECREASING([y] + b) && (x <= y) ==> IS_NONDECREASING(((a + [x]) + [y]) + b));");
				out.newLine();
				out.write("assume (forall a:seq<int>, b: seq<int>, x:int, y:int :: IS_NONDECREASING(a + [x]) && IS_NONDECREASING([y] + b) && (x <= y) ==> IS_NONDECREASING((a + [x]) + ([y] + b)));");
				out.newLine();
				out.write("assume (forall a:seq<int>, b: seq<int>, c: seq<int> :: IS_NONDECREASING(a + c) && IS_NONDECREASING(c + b) && c!= [] ==> IS_NONDECREASING(a + c + b));");
				out.newLine();
				out.write("assume (forall a:seq<int>, b: seq<int>, c: seq<int> :: IS_NONDECREASING(a + c) && IS_NONDECREASING(c + b) && c!= [] ==> IS_NONDECREASING((a + c) + b));");
				out.newLine();
				out.write("assume (forall a:seq<int>, b: seq<int>, c: seq<int> :: IS_NONDECREASING(a + c) && IS_NONDECREASING(c + b) && c!= [] ==> IS_NONDECREASING(a + (c + b)));");
				out.newLine();
				out.write("assume (forall a:seq<int>, b: seq<int>, c: seq<int> :: IS_NONDECREASING(a + b +c) ==> IS_NONDECREASING(a + b) && IS_NONDECREASING(b + c) && IS_NONDECREASING(a + c));");
				out.newLine();
				out.write("assume (forall a:seq<int>, b: seq<int>, c: seq<int> :: IS_NONDECREASING((a + b) +c) ==> IS_NONDECREASING(a + b) && IS_NONDECREASING(b + c) && IS_NONDECREASING(a + c));");
				out.newLine();
				out.write("assume (forall a:seq<int>, b: seq<int>, c: seq<int> :: IS_NONDECREASING(a + (b +c)) ==> IS_NONDECREASING(a + b) && IS_NONDECREASING(b + c) && IS_NONDECREASING(a + c));");
				out.newLine();
				out.write("assume (forall a: seq<int>, x: int, y: int :: IS_NONDECREASING([x] + a + [y]) ==> (x <= y) );"); 
				out.newLine();
				out.write("assume(forall a: seq<int>, x: int, y: int :: (x <= y) && IS_NONDECREASING([y] + a) ==> IS_NONDECREASING([x] + a) );");
				out.newLine();
				out.newLine();
			}	
			if(var_decld.contains("ARE_PERMUTATIONS"))
			{
				out.newLine();	
				out.write("//definition of ARE_PERMUTATIONS");
				out.newLine();
				out.write("assume (forall s1: seq<int>, s2: seq<int> :: ARE_PERMUTATIONS(s1, s2) == (forall i: int :: OCCURS_COUNT(s1, i) == OCCURS_COUNT(s2, i))) ;  ");		
				out.newLine();
				out.write("//ARE_PERMUTATIONS lemmas");
				out.newLine();
				out.write("assume (forall a:seq<int> , b: seq<int> :: a == b ==> ARE_PERMUTATIONS(a, b));");
				out.newLine();
				out.write("assume (forall a:seq<int> :: ARE_PERMUTATIONS(a, a));");
				out.newLine();
				out.write("assume (forall a:seq<int>, b: seq<int>, c: seq<int> :: ARE_PERMUTATIONS(a, b) && ARE_PERMUTATIONS(b, c) ==> ARE_PERMUTATIONS(a, c));");
				out.newLine();
				out.write("assume (forall a:seq<int>, b: seq<int>, c :seq<int> :: ARE_PERMUTATIONS((a + b) + c, a + (b + c)));"); 
				out.newLine();
				out.write("assume (forall a:seq<int>, b: seq<int>, c :seq<int> :: ARE_PERMUTATIONS(a + (b + c), b + (a + c))); ");
				out.newLine();
				out.write("assume (forall a:seq<int>, b: seq<int> :: ARE_PERMUTATIONS(a, b) ==> ARE_PERMUTATIONS(b, a));");
				out.newLine();
				out.write("assume (forall a:seq<int>, b:seq<int> :: ARE_PERMUTATIONS(a, b) ==>  |a| == |b|); ");
				out.newLine();
				out.write("assume (forall a:seq<int>, b: seq<int> :: ARE_PERMUTATIONS(a + [] , b) ==> ARE_PERMUTATIONS(a , b));");
				out.newLine();
				out.write("assume (forall a:seq<int>, b: seq<int> :: ARE_PERMUTATIONS([] + a , b) ==> ARE_PERMUTATIONS(a , b)); ");
				out.newLine();
				out.write("assume (forall a:seq<int>, b: seq<int> :: ARE_PERMUTATIONS(a , [] + b ) ==> ARE_PERMUTATIONS(a , b)); ");
				out.newLine();
				out.write("assume (forall a:seq<int>, b: seq<int> :: ARE_PERMUTATIONS(a , b + []) ==> ARE_PERMUTATIONS(a , b));");
				out.newLine();				 
				out.write("assume(forall a:seq<int>, b: seq<int>, c: seq<int>, d: seq<int>, e: seq<int>, f: seq<int>,g: seq<int>, h:seq<int>, i:seq<int> :: ARE_PERMUTATIONS((((a + (b + c)) + d) + e), (((f + g) + h) + i)) ==> ARE_PERMUTATIONS(((((a + e) + d) + c) + b), (((f + g) + h) + i)));");
				out.newLine();
				out.write("assume(forall a:seq<int>, b: seq<int>, c: seq<int>, d: seq<int>, e: seq<int> :: ARE_PERMUTATIONS((((a + (b + c)) + d) + e), ((c + (d + a)) + (e + b))));");
				out.newLine();
				out.write("assume(forall a:seq<int>, b: seq<int>, c: seq<int>, d: seq<int>, e: seq<int> :: ARE_PERMUTATIONS((((a + (b+ c)) + d) + e),((((a + b) + c) + d) +e)));");
				out.newLine();
				out.write("assume(forall a:seq<int>, b: seq<int>, c: seq<int>, d: seq<int>, e: seq<int> ::  ARE_PERMUTATIONS((((a + (b+ c)) +d) + e),((((a + e) + d) + c) +b)));");
				out.newLine();
				out.write("assume (forall a:seq<int>, b:seq<int>, c:seq<int>, d:seq<int> :: ARE_PERMUTATIONS(a, (b+c)) && ARE_PERMUTATIONS(c, d)==> ARE_PERMUTATIONS(a, (b+ d)));");
				out.newLine();
				out.write("assume (forall a:seq<int>, b:seq<int>, c:seq<int>, d:seq<int> :: ARE_PERMUTATIONS(a, (b+c)) && ARE_PERMUTATIONS(b, d)==> ARE_PERMUTATIONS(a, (d+ c)));");
				out.newLine();
				out.write("assume (forall a:seq<int>, b:seq<int>, c:seq<int>, d:seq<int> :: ARE_PERMUTATIONS(a, (b+c)) &&  ARE_PERMUTATIONS((b + c), d) ==> ARE_PERMUTATIONS(a, d));");
				out.newLine();
				out.newLine();
			}	
		}
		else
		{
			if(var_decld.contains("ARE_IN_ORDER"))
			{
				out.newLine();	
				out.write("//definition of ARE_IN_ORDER");
				out.newLine();
				out.write("assume (forall x, y  :: ARE_IN_ORDER(x, y) || ARE_IN_ORDER(y, x));");
				out.newLine();	
				out.write("assume (forall x, y, z :: (ARE_IN_ORDER(x, y) && ARE_IN_ORDER(y, z) ==> ARE_IN_ORDER(x, z)));");		
				out.newLine();
			}

			if(var_decld.contains("OCCURS_COUNT"))
			{
				out.newLine();
				out.write("//definition of OCCURS_COUNT");
				out.newLine();
				out.write("assume ( forall s:seq<T>, i :T :: if s == [] then OCCURS_COUNT(s, i) == 0 else (exists x: T, r: seq<T> :: s == [x] + r && (if x == i then OCCURS_COUNT(s, i) == OCCURS_COUNT(r, i) +1 else OCCURS_COUNT(s, i) == OCCURS_COUNT(r, i))));	");		
				out.newLine();
			}
			if(var_decld.contains("PRECEDES"))
			{
				out.newLine();	
				out.write("//definition of PRECEDES");
				out.newLine();
				out.write("assume (forall s1: seq<T>, s2: seq<T>:: PRECEDES(s1, s2) == (forall i, j :: (OCCURS_COUNT(s1, i) > 0 && OCCURS_COUNT(s2, j) > 0 ==> ARE_IN_ORDER(i, j)))) ;	");		
				out.newLine();
				out.write("//PRECEDES lemmas");
				out.newLine();
				out.write("assume (forall x:seq<T> :: PRECEDES([], x));");
				out.newLine();
				out.write("assume (forall x:seq<T> :: PRECEDES(x, []));");
				out.newLine();			
				out.write("assume (forall a: T, b: T :: ARE_IN_ORDER(a, b) ==> PRECEDES([a], [b]));");
				out.newLine();
				out.write("assume(forall x: seq<T>, a: T, b: T :: ARE_IN_ORDER(a, b) && PRECEDES(x, [b]) ==> PRECEDES(x + [a], [b]) );");
				out.newLine();
				out.newLine();
			}
			if(var_decld.contains("IS_NONDECREASING"))
			{
				out.newLine();	
				out.write("//definition of IS_NONDECREASING");
				out.newLine();
				out.write("assume (forall s: seq<T>:: IS_NONDECREASING(s) == (forall a: seq<T> , b: seq<T> :: s == a + b ==> PRECEDES(a, b))); ");		

			}
			if(var_decld.contains("ARE_PERMUTATIONS"))
			{
				out.newLine();	
				out.write("//definition of ARE_PERMUTATIONS");
				out.newLine();	
				out.write("assume (forall s1: seq<T>, s2: seq<T>:: ARE_PERMUTATIONS(s1, s2) == (forall i :: OCCURS_COUNT(s1, i) == OCCURS_COUNT(s2, i))) ;");		
				out.newLine();

			}
		}//end else

		if(var_decld.contains("IS_PRECEDING"))
		{
			out.newLine();	
			out.write("assume (forall x: set<T> :: IS_PRECEDING({}, x));");
			out.newLine();
			out.write("	assume (forall x: set<T> :: IS_PRECEDING(x, {}));");
			out.newLine();
			out.write("assume (forall x: set<T>, y: set<T> :: IS_PRECEDING(x, y) || IS_PRECEDING(y, x));");
			out.newLine();
			out.write("assume (forall x:set<T>, y: set<T>, s: set<T>, t:set<T> :: (y == t + s && IS_PRECEDING(x, y)) ==> (IS_PRECEDING(x, t) && IS_PRECEDING(y, t)));");
			out.newLine();
			out.write("assume (forall x:set<T>, y: set<T>, s: set<T>, t:set<T> :: (x == t + s && IS_PRECEDING(x, y)) ==> (IS_PRECEDING(t, y) && IS_PRECEDING(s, y)));");
			out.newLine();
		}
		if(var_decld.contains("elements"))
		{
			out.write("	assume (forall s:seq<T> :: if s ==[] then elements(s) == {} else (exists t: seq<T>, x: T :: s == [x] + t && elements(s) == {x} + elements(t)));");
			out.newLine();
		}

		if(var_decld.contains("IS_ODD"))
		{
			out.write("//is_odd definition");
			out.write("assume (forall n :: IS_ODD(n) ==> (exists k :: n == 2*k + 1)) ;");
			out.newLine();
			out.write("//  is_odd lemmas");
			out.write("assume (forall k :: IS_ODD(k) != IS_ODD(k+1));");
			out.newLine();
			out.write("assume (forall k :: k>=0 && IS_ODD(k) ==> k>0);");
			out.newLine();
			out.write("assume (forall k :: k>0 && !IS_ODD(k) ==> k>1);");
			out.newLine();
			out.newLine();
		}
		if(var_decld.contains("SUBSTRING_REPLACEMENT") )
		{
			out.write("// substring_replacement definition");
			out.newLine();
			out.write("assume ( forall s: seq<T>, ss: seq<T>, start: int, finish: int :: (start <0 || start > finish || finish > |s|) ==> SUBSTRING_REPLACEMENT(s, ss, start, finish) == s &&(!(start <0 || start > finish || finish > |s|) ==> (exists a:seq<T>, b:seq<T>, c:seq<T> :: s == a + b + c && |a| == start && |c| == |s| - finish && SUBSTRING_REPLACEMENT(s, ss, start, finish) == a + ss + c)));");
			out.newLine();	
		}

		if(var_decld.contains("DIFFER_BY_ONE") && var_decld.contains("SAME_EXCEPT_AT") && var_decld.contains("SUBSTRING_REPLACEMENT") )
		{
			out.newLine();
			out.write("//differ_by_one definition");
			out.newLine();
			out.write("assume ( forall t1: seq<T>, t2: seq<T>, pos: int, ch: T :: (DIFFER_BY_ONE(t1, t2, pos, ch)) == (exists a: seq<T>, b : seq<T> :: t1 == (a + b) && t2 == (a + [ch] + b) && |a| == pos));");
			out.newLine();
			out.write("// same_except_at definition");
			out.newLine();
			out.write("assume ( forall t1: seq<T>, t2: seq<T>, pos: int, x: T , y: T:: (SAME_EXCEPT_AT(t1, t2, pos, x, y)) == (exists a: seq<T>, b : seq<T> :: t1 == (a + [x] + b) && t2 == (a + [y] + b) && |a| == pos)); ");
			out.newLine();

			out.write("//differ_by_one lemmas");
			out.newLine();
			out.write("assume (forall s1: seq<T>, s2: seq<T>, pos: int, x: T :: DIFFER_BY_ONE(s1, s2, pos, x) && 0 <= pos && pos < |s2| ==> |s1| == |s2| - 1);");
			out.newLine();
			out.write("assume (forall s1: seq<T>, s2: seq<T>, x: T :: DIFFER_BY_ONE(s1, s2, 0, x) && |s2| > 0 ==> (s2 == [x] + s1));");
			out.newLine();
			out.write("assume (forall s1: seq<T>, s2: seq<T>, x: T :: DIFFER_BY_ONE(s1, s2, |s1|, x) ==> (s1 + [x] == s2));");
			out.newLine();
			out.write("assume (forall s1: seq<T>, s2: seq<T>, x: T :: DIFFER_BY_ONE(s1, s2, |s2|-1 , x)  ==> (s1 + [x] == s2));");
			out.newLine();
			out.write("assume (forall s1: seq<T>, s2: seq<T>, x: T :: DIFFER_BY_ONE( (s1 + s2), (s1 + [x] + s2), |s1|, x)) ;");
			out.newLine();
			out.write("assume (forall s1: seq<T>, s2: seq<T>, x: T , y: T :: SAME_EXCEPT_AT( (s1 + [x] + s2), (s1 + [y] + s2), |s1|, x, y));");
			out.newLine();
			out.write("assume (forall s: seq<T>, start: int :: s == SUBSTRING_REPLACEMENT(s, [], start, start));");
			out.newLine();
			out.write("assume (forall s1: seq<T>, s2: seq<T>, start: int, finish: int, x: T :: DIFFER_BY_ONE(s1, s2, start, x) ==> (SUBSTRING_REPLACEMENT(s1, [], start, (finish - 1)) == SUBSTRING_REPLACEMENT(s2, [], start, finish)));");
			out.newLine();
			out.newLine();
		}

		if(var_decld.contains("SUBSTRING"))
		{
			out.newLine();
			out.write("//substring definition");
			out.newLine();	
			out.write("assume ( forall s: seq<T>, start : int, finish: int ::(start < 0 || start > finish || finish > |s| ==> SUBSTRING(s, start, finish) == []) && (!(start < 0 || start > finish || finish > |s|) ==> (exists a:seq<T>, b:seq<T> :: s == a + SUBSTRING(s, start, finish) + b && |a| == start&& |b| == |s| - finish)));");
			out.newLine();			
			out.write("//substring lemmas");
			out.newLine();	
			out.write("assume (forall s: seq<T>, start: int, finish: int :: start < 0 || start > finish || finish > |s| ==> SUBSTRING(s, start, finish) == []);");
			out.newLine();
			out.write("assume (forall s: seq<T>, start: int, finish: int :: |s| == 0 ==> SUBSTRING(s, start, finish) == []);");
			out.newLine();
			out.write("assume (forall m: int, n: int, a: seq<T> :: 0 <= m && m <= n && n <= |a| ==> SUBSTRING(a, 0, m) + SUBSTRING(a, m, n) == SUBSTRING(a, 0, n));");
			out.newLine();
			out.write("assume (forall m: int, n: int, a: seq<T> :: 0 <= m && m <= n && n <= |a| ==> SUBSTRING(a, 0, m) + SUBSTRING(a, m, n) + SUBSTRING(a, n, |a|) == a);");
			out.newLine();
			out.write("assume (forall j: int, k: int, s1: seq<T>, s2: seq<T> :: 0 <= j && j <= k && k <= |s1| ==> SUBSTRING(s1 + s2, j, k) == SUBSTRING(s1, j, k));");
			out.newLine();
			out.write("assume (forall j: int, k: int, s1: seq<T>, s2: seq<T> :: |s1| <= j && j <= k && k <= (|s1| + |s2|) ==> SUBSTRING(s1 + s2, j, k) == SUBSTRING(s2, j - |s1|, k - |s1|));");
			out.newLine();
			out.newLine();
		}

		if(var_decld.contains("FUNCTION"))
		{
			out.newLine();
			out.write("assume (FUNCTION({}) == {});");
			out.newLine();
			out.write("assume (forall s:set<T>, t: set<T> :: FUNCTION(s + t) == FUNCTION(s) + FUNCTION(t));");
			out.newLine();
		}
		if(var_decld.contains("HAS_ONLY_DIGITS"))
		{
			out.newLine();
			out.write("//definition of HAS_ONLY_DIGITS");
			out.newLine();
			out.write("assume ( forall digits: seq<int>, radix: int :: (HAS_ONLY_DIGITS(digits, radix)) == (forall d: int, r : seq<int> :: digits == [d] + r && 0 <= d && d < radix && HAS_ONLY_DIGITS(r, radix))); ");
			out.newLine();
		}

		if(var_decld.contains("NUMERICAL_VALUE"))
		{
			out.newLine();
			out.write("//definition of NUMERICAL_VALUE");
			out.newLine();
			out.write("assume ( forall s:seq<int>, r :int :: if s == [] then NUMERICAL_VALUE(s, r) == 0 else (forall k: seq<int>, d: int :: s == k + [d] && NUMERICAL_VALUE(s, r) == NUMERICAL_VALUE(k, r) * r + d));");
			out.newLine();
			out.write("//lemmas");
			out.newLine();
			out.write("assume (forall radix: int:: radix>1 ==>  NUMERICAL_VALUE([], radix) == 0);");
			out.newLine();
			out.write("assume (forall digits : seq<int>, radix: int, x: int :: radix>1 && x >= 0 && x < radix ==>  (((NUMERICAL_VALUE(digits, radix) * radix) + x) == NUMERICAL_VALUE(digits+[x], radix))) ;");
			out.newLine();
			out.newLine();
		}

		if(var_decld.contains("IS_WELL_FORMED_FUNCTION"))
		{
			out.newLine();
			out.write("//definition of IS_WELL_FORMED_FUNCTION");
			out.newLine();
			out.write("assume ( forall digits: seq<int>, radix: int :: (IS_WELL_FORMED_FUNCTION(digits, radix)) == (forall d: int, r : seq<int> :: digits == [d] + r && 0 < d && d < radix && HAS_ONLY_DIGITS(r, radix))); ");
			out.newLine();
			out.write("//lemmas");
			out.newLine();
			out.write("assume (forall radix: int:: radix>1 ==> IS_WELL_FORMED_FUNCTION([], radix));");
			out.newLine();
			out.write("assume (forall digits : seq<int>, radix: int, x: int :: radix>1 && x >= 0 && x < radix && IS_WELL_FORMED_FUNCTION(digits, radix) ==> IS_WELL_FORMED_FUNCTION(digits+[x], radix)) ;");
			out.newLine();
		}*/

}

/*	public void declare_other_lemmas (Document doc) throws IOException
	{
		if(string_object == 1)
		{
			if(fun_decld.contains("IS_NONDECREASING"))
			{
				out.newLine();
				out.write("//IS_NONDECREASING lemmas ");
				out.newLine();
				out.write("assume (IS_NONDECREASING([]));");
				out.newLine();
				out.write("assume (forall x:T :: IS_NONDECREASING([x]));");
				out.newLine();
				out.write("assume (forall q: seq<T> :: |q| <= 1 ==> IS_NONDECREASING(q));");
				out.newLine();			
				out.write("assume (forall x:seq<T> :: IS_NONDECREASING([]+x) <==> IS_NONDECREASING(x));");
				out.newLine();
				out.write("assume (forall x:seq<T> :: IS_NONDECREASING(x+[])  <==> IS_NONDECREASING(x));");
				out.newLine();
				out.write("assume (forall a: T, b: T :: ARE_IN_ORDER(a, b) ==> IS_NONDECREASING([a] + [b]));"); 
				out.newLine();
				out.write("assume (forall x: seq<T>, y: seq<T> :: IS_NONDECREASING(x+y) ==> IS_NONDECREASING(x) && IS_NONDECREASING (y));"); 
				out.newLine();
				out.write("assume (forall x: seq<T>, y: seq<T>, z: seq<T> :: IS_NONDECREASING(x+y+z) ==> IS_NONDECREASING(x + z) && IS_NONDECREASING(y + z) && IS_NONDECREASING(x + y));"); 
				out.newLine();
				out.write("assume(forall a: seq<T>, b:seq<T>, x: T, y:T :: IS_NONDECREASING(a + [y]) && IS_NONDECREASING([y] + b) ==> IS_NONDECREASING(a + [y] + b));");
				out.newLine();
				out.write("assume (forall a:seq<T>, b: seq<T>, x:T, y:T :: IS_NONDECREASING(a + [x]) && IS_NONDECREASING([y] + b) && ARE_IN_ORDER(x, y) ==> IS_NONDECREASING(a + [x] + [y] + b));");
				out.newLine();
				out.write("assume (forall a:seq<T>, b: seq<T>, x:T, y:T :: IS_NONDECREASING(a + [x]) && IS_NONDECREASING([y] + b) && ARE_IN_ORDER(x, y) ==> IS_NONDECREASING(a + ([x] + ([y] + b))));");
				out.newLine();
				out.write("assume (forall a:seq<T>, b: seq<T>, x:T, y:T :: IS_NONDECREASING(a + [x]) && IS_NONDECREASING([y] + b) && ARE_IN_ORDER(x, y) ==> IS_NONDECREASING(((a + [x]) + [y]) + b));");
				out.newLine();
				out.write("assume (forall a:seq<T>, b: seq<T>, x:T, y:T :: IS_NONDECREASING(a + [x]) && IS_NONDECREASING([y] + b) && ARE_IN_ORDER(x, y) ==> IS_NONDECREASING((a + [x]) + ([y] + b)));");
				out.newLine();
				out.write("assume (forall a:seq<T>, b: seq<T>, c: seq<T> :: IS_NONDECREASING(a + c) && IS_NONDECREASING(c + b) && c!= [] ==> IS_NONDECREASING(a + c + b));");
				out.newLine();
				out.write("assume (forall a:seq<T>, b: seq<T>, c: seq<T> :: IS_NONDECREASING(a + c) && IS_NONDECREASING(c + b) && c!= [] ==> IS_NONDECREASING((a + c) + b));");
				out.newLine();
				out.write("assume (forall a:seq<T>, b: seq<T>, c: seq<T> :: IS_NONDECREASING(a + c) && IS_NONDECREASING(c + b) && c!= [] ==> IS_NONDECREASING(a + (c + b)));");
				out.newLine();
				out.write("assume (forall a:seq<T>, b: seq<T>, c: seq<T> :: IS_NONDECREASING(a + b +c) ==> IS_NONDECREASING(a + b) && IS_NONDECREASING(b + c) && IS_NONDECREASING(a + c));");
				out.newLine();
				out.write("assume (forall a:seq<T>, b: seq<T>, c: seq<T> :: IS_NONDECREASING((a + b) +c) ==> IS_NONDECREASING(a + b) && IS_NONDECREASING(b + c) && IS_NONDECREASING(a + c));");
				out.newLine();
				out.write("assume (forall a:seq<T>, b: seq<T>, c: seq<T> :: IS_NONDECREASING(a + (b +c)) ==> IS_NONDECREASING(a + b) && IS_NONDECREASING(b + c) && IS_NONDECREASING(a + c));");
				out.newLine();
				out.write("assume (forall a: seq<T>, x: T, y: T :: IS_NONDECREASING([x] + a + [y]) ==> ARE_IN_ORDER(x, y) );"); 
				out.newLine();
				out.write("assume(forall a: seq<T>, x: T, y: T :: ARE_IN_ORDER(x, y) && IS_NONDECREASING([y] + a) ==> IS_NONDECREASING([x] + a) );");
				out.newLine();
				out.newLine();
			}

			if(fun_decld.contains("IS_NONDECREASING"))
			{
				out.write("//ARE_PERMUTATIONS lemmas");
				out.newLine();
				out.write("assume (forall a:seq<T> , b: seq<T> :: a == b ==> ARE_PERMUTATIONS(a, b));");
				out.newLine();
				out.write("assume (forall a:seq<T> :: ARE_PERMUTATIONS(a, a));");
				out.newLine();
				out.write("assume (forall a:seq<T>, b: seq<T>, c: seq<T> :: ARE_PERMUTATIONS(a, b) && ARE_PERMUTATIONS(b, c) ==> ARE_PERMUTATIONS(a, c));");
				out.newLine();
				out.write("assume (forall a:seq<T>, b: seq<T>, c :seq<T> :: ARE_PERMUTATIONS((a + b) + c, a + (b + c)));"); 
				out.newLine();
				out.write("assume (forall a:seq<T>, b: seq<T>, c :seq<T> :: ARE_PERMUTATIONS(a + (b + c), b + (a + c)));"); 
				out.newLine();
				out.write("assume (forall a:seq<T>, b: seq<T> :: ARE_PERMUTATIONS(a, b) ==> ARE_PERMUTATIONS(b, a));");
				out.newLine();
				out.write("assume (forall a:seq<T>, b:seq<T> :: ARE_PERMUTATIONS(a, b) ==>  |a| == |b|);"); 
				out.newLine();
				out.write("assume (forall a:seq<T>, b: seq<T> :: ARE_PERMUTATIONS(a + [] , b) ==> ARE_PERMUTATIONS(a , b));");
				out.newLine();
				out.write("assume (forall a:seq<T>, b: seq<T> :: ARE_PERMUTATIONS([] + a , b) ==> ARE_PERMUTATIONS(a , b)); ");
				out.newLine();
				out.write("assume (forall a:seq<T>, b: seq<T> :: ARE_PERMUTATIONS(a , [] + b ) ==> ARE_PERMUTATIONS(a , b)); ");
				out.newLine();
				out.write("assume (forall a:seq<T>, b: seq<T> :: ARE_PERMUTATIONS(a , b + [])==> ARE_PERMUTATIONS(a , b));");
				out.newLine();			 
				out.write("assume(forall a:seq<T>, b: seq<T>, c: seq<T>, d: seq<T>, e: seq<T>, f: seq<T>,g: seq<T>, h:seq<T>, i:seq<T> :: ARE_PERMUTATIONS((((a + (b + c)) + d) + e), (((f + g) + h) + i)) ==> ARE_PERMUTATIONS(((((a + e) + d) + c) + b), (((f + g) + h) + i)));");
				out.newLine();
				out.write(" assume(forall a:seq<T>, b: seq<T>, c: seq<T>, d: seq<T>, e: seq<T> :: ARE_PERMUTATIONS((((a + (b + c)) + d) + e), ((c + (d + a)) + (e + b))));");
				out.newLine();
				out.write(" assume(forall a:seq<T>, b: seq<T>, c: seq<T>, d: seq<T>, e: seq<T> :: ARE_PERMUTATIONS((((a + (b+ c)) + d) + e),((((a + b) + c) + d) +e)));");
				out.newLine();
				out.write(" assume(forall a:seq<T>, b: seq<T>, c: seq<T>, d: seq<T>, e: seq<T> ::  ARE_PERMUTATIONS((((a + (b+ c)) +d) + e),((((a + e) + d) + c) +b)));");
				out.newLine();
				out.write("assume (forall a:seq<T>, b:seq<T>, c:seq<T>, d:seq<T> :: ARE_PERMUTATIONS(a, (b+c)) && ARE_PERMUTATIONS(c, d)==> ARE_PERMUTATIONS(a, (b+ d)));");
				out.newLine();
				out.write("assume (forall a:seq<T>, b:seq<T>, c:seq<T>, d:seq<T> :: ARE_PERMUTATIONS(a, (b+c)) && ARE_PERMUTATIONS(b, d)==> ARE_PERMUTATIONS(a, (d+ c)));");
				out.newLine();
				out.write("assume (forall a:seq<T>, b:seq<T>, c:seq<T>, d:seq<T> :: ARE_PERMUTATIONS(a, (b+c)) &&  ARE_PERMUTATIONS((b + c), d) ==> ARE_PERMUTATIONS(a, d));");
				out.newLine();
				out.newLine();
			}
		}
	}*/
}
