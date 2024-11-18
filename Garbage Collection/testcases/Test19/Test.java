class Test
{
	static class Element
	{
		int data;
		Element next;
		Element()
		{
			data=0;
			next=null;
		}
		Element(int d)
		{
			data=d;
			next=null;
		}
	}
	static void L(int p,int q,Element obj)
	{
		Element x=new Element();
		Element y= new Element();
		Element o=new Element();
		if(p>q)
		{
			o.next=x;
		}
		else
		{
			o.next=y;
		}
		obj.next=y;
		
	}
	public static void main(String[] args) {
		Element obj=new Element();
		L(10,20,obj);
	}
}
