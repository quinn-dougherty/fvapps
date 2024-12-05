import Link from "next/link";
import { getDataset } from "@/utils/hf";

async function getSample(id: string) {
  const dataset = await getDataset();
  return dataset.splits[0].samples[parseInt(id)];
}

export default async function SamplePage({
  params,
}: {
  params: { id: string };
}) {
  const sample = await getSample(params.id);

  return (
    <div className="p-8">
      <Link href="/" className="text-blue-600 hover:underline mb-4 block">
        ← Back to all samples
      </Link>
      <h1 className="text-2xl font-bold mb-4">Sample {params.id}</h1>
      <pre className="bg-gray-100 p-4 rounded overflow-auto">
        {JSON.stringify(sample, null, 2)}
      </pre>
    </div>
  );
}
